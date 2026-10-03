/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch005`.
* `GerverSofa.KernelOnly.PartE.Certificates.Batch027`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells0d991a929b

/-- Subcell `0000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0001` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0001 : AngleCell :=
  childLH (childLL (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0002` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0002 : AngleCell :=
  childHL (childLL (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0003` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0003 : AngleCell :=
  childHH (childLL (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0012` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0012 : AngleCell :=
  childHL (childLH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0013` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0013 : AngleCell :=
  childHH (childLH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0030` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0030 : AngleCell :=
  childLL (childHH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0031` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0031 : AngleCell :=
  childLH (childHH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0032` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0032 : AngleCell :=
  childHL (childHH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0033` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0033 : AngleCell :=
  childHH (childHH (childLL (childLL e24PhiAboveRoot)))

/-- Subcell `0100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0101 : AngleCell :=
  childLH (childLL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0102` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0102 : AngleCell :=
  childHL (childLL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0103` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0103 : AngleCell :=
  childHH (childLL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0112` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0112 : AngleCell :=
  childHL (childLH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0113` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0113 : AngleCell :=
  childHH (childLH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0120` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0120 : AngleCell :=
  childLL (childHL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0121` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0121 : AngleCell :=
  childLH (childHL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0122` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0122 : AngleCell :=
  childHL (childHL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0123` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0123 : AngleCell :=
  childHH (childHL (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0130` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0130 : AngleCell :=
  childLL (childHH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0131` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0131 : AngleCell :=
  childLH (childHH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0132` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0132 : AngleCell :=
  childHL (childHH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `0133` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell0133 : AngleCell :=
  childHH (childHH (childLH (childLL e24PhiAboveRoot)))

/-- Subcell `1000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1001` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1001 : AngleCell :=
  childLH (childLL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1002` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1002 : AngleCell :=
  childHL (childLL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1003` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1003 : AngleCell :=
  childHH (childLL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1010 : AngleCell :=
  childLL (childLH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1011 : AngleCell :=
  childLH (childLH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1012` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1012 : AngleCell :=
  childHL (childLH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1013` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1013 : AngleCell :=
  childHH (childLH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1020` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1020 : AngleCell :=
  childLL (childHL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1021` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1021 : AngleCell :=
  childLH (childHL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1022` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1022 : AngleCell :=
  childHL (childHL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1023` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1023 : AngleCell :=
  childHH (childHL (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1030` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1030 : AngleCell :=
  childLL (childHH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1031` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1031 : AngleCell :=
  childLH (childHH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1032` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1032 : AngleCell :=
  childHL (childHH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1033` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1033 : AngleCell :=
  childHH (childHH (childLL (childLH e24PhiAboveRoot)))

/-- Subcell `1100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1100 : AngleCell :=
  childLL (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1102` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1102 : AngleCell :=
  childHL (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1103` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1103 : AngleCell :=
  childHH (childLL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1112` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1112 : AngleCell :=
  childHL (childLH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1113` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1113 : AngleCell :=
  childHH (childLH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1120` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1120 : AngleCell :=
  childLL (childHL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1121` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1121 : AngleCell :=
  childLH (childHL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1122` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1122 : AngleCell :=
  childHL (childHL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1123` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1123 : AngleCell :=
  childHH (childHL (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1130` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1130 : AngleCell :=
  childLL (childHH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1131` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1131 : AngleCell :=
  childLH (childHH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1132` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1132 : AngleCell :=
  childHL (childHH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `1133` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1133 : AngleCell :=
  childHH (childHH (childLH (childLH e24PhiAboveRoot)))

/-- Subcell `3221` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3221 : AngleCell :=
  childLH (childHL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3222` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3222 : AngleCell :=
  childHL (childHL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3223` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3223 : AngleCell :=
  childHH (childHL (childHL (childHH e24PhiBelowRoot)))

/-- Subcell `3310` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3310 : AngleCell :=
  childLL (childLH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3311` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3311 : AngleCell :=
  childLH (childLH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `3313` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3313 : AngleCell :=
  childHH (childLH (childHH (childHH e24PhiBelowRoot)))

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell0000)))

/-- Subcell `00002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell0000)))

/-- Subcell `00002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell0000)))

/-- Subcell `00002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell0000)))

/-- Subcell `00002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell0000)))

/-- Subcell `00002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell0000)))

/-- Subcell `00002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell0000)))

/-- Subcell `00002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell0000)))

/-- Subcell `00002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell0000)))

/-- Subcell `00002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell0000)))

/-- Subcell `00002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell0000)))

/-- Subcell `00002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell0000)))

/-- Subcell `00002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell0000)))

/-- Subcell `00002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell0000)))

/-- Subcell `00002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell0000)))

/-- Subcell `00002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell0000)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell0000)))

/-- Subcell `00003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell0000)))

/-- Subcell `00003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell0000)))

/-- Subcell `00003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell0000)))

/-- Subcell `00003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell0000)))

/-- Subcell `00003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell0000)))

/-- Subcell `00003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell0000)))

/-- Subcell `00003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell0000)))

/-- Subcell `00003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell0000)))

end GerverSofa.PartE.CertificateCells0d991a929b

namespace GerverSofa.PartE.CertificateCells802ef10e9d

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell0000)))

/-- Subcell `00003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `000023102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00002310)))

/-- Subcell `000023102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00002310)))

/-- Subcell `000023103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00002310)))

/-- Subcell `000023103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002310)))

/-- Subcell `000023110220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00002311)))

/-- Subcell `000023110221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00002311)))

/-- Subcell `000023110222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00002311)))

/-- Subcell `000023110223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00002311)))

/-- Subcell `000023110230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00002311)))

/-- Subcell `000023110231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00002311)))

/-- Subcell `000023110232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00002311)))

/-- Subcell `000023110233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00002311)))

/-- Subcell `000023110320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00002311)))

/-- Subcell `000023110321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00002311)))

/-- Subcell `000023110322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00002311)))

/-- Subcell `000023110323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00002311)))

/-- Subcell `000023110330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00002311)))

/-- Subcell `000023110331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00002311)))

/-- Subcell `000023110332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00002311)))

/-- Subcell `000023110333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023110333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00002311)))

/-- Subcell `000023111220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00002311)))

/-- Subcell `000023111221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00002311)))

/-- Subcell `000023111222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00002311)))

/-- Subcell `000023111223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00002311)))

/-- Subcell `000023111230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaAboveCell00002311)))

/-- Subcell `000023111231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaAboveCell00002311)))

/-- Subcell `000023111232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaAboveCell00002311)))

/-- Subcell `000023111233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaAboveCell00002311)))

/-- Subcell `000023111320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaAboveCell00002311)))

/-- Subcell `000023111321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaAboveCell00002311)))

/-- Subcell `000023111322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaAboveCell00002311)))

/-- Subcell `000023111323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaAboveCell00002311)))

/-- Subcell `000023111330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaAboveCell00002311)))

/-- Subcell `000023111331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaAboveCell00002311)))

/-- Subcell `000023111332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaAboveCell00002311)))

/-- Subcell `000023111333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023111333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaAboveCell00002311)))

/-- Subcell `000023112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00002311)))

/-- Subcell `000023112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00002311)))

/-- Subcell `000023113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00002311)))

/-- Subcell `000023113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000023113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002311)))

/-- Subcell `000032000220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00003200)))

/-- Subcell `000032000221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00003200)))

/-- Subcell `000032000222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00003200)))

/-- Subcell `000032000223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00003200)))

/-- Subcell `000032000230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00003200)))

/-- Subcell `000032000231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00003200)))

/-- Subcell `000032000232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00003200)))

/-- Subcell `000032000233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00003200)))

/-- Subcell `000032000320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00003200)))

/-- Subcell `000032000321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00003200)))

/-- Subcell `000032000322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00003200)))

/-- Subcell `000032000323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00003200)))

/-- Subcell `000032000330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00003200)))

/-- Subcell `000032000331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00003200)))

/-- Subcell `000032000332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00003200)))

/-- Subcell `000032000333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032000333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00003200)))

/-- Subcell `000032001220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032001220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00003200)))

/-- Subcell `000032001221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032001221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00003200)))

/-- Subcell `000032001222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032001222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00003200)))

/-- Subcell `000032001223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032001223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00003200)))

/-- Subcell `000032002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003200)))

/-- Subcell `000032002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003200)))

/-- Subcell `000032003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003200)))

/-- Subcell `000032003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003200)))

/-- Subcell `000032003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003200)))

end GerverSofa.PartE.CertificateCells802ef10e9d

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT000001`.
-/

public section

noncomputable section

section

/-! E24KC5 checkpoint-aware kernel batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0d991a929b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0d991a929b

open CertificateCells0d991a929b

theorem e24KC2PhiAboveLeaf00000 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0000) = true := by
  have h : physicallyIrrelevant (childLL phiAboveCell0000) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 11 (childLL phiAboveCell0000) h
theorem e24KC2PhiAboveLeaf00001 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0000) = true := by
  have h : ((childLH phiAboveCell0000)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell0000) h

theorem e24KC2PhiAboveLeaf00002 :
    adaptiveCoverCheck 11 (childHL phiAboveCell0000) = true := by
  have h : physicallyIrrelevant (childHL phiAboveCell0000) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 11 (childHL phiAboveCell0000) h

theorem e24KC2PhiAboveLeaf00003 :
    adaptiveCoverCheck 11 (childHH phiAboveCell0000) = true := by
  have h : physicallyIrrelevant (childHH phiAboveCell0000) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 11 (childHH phiAboveCell0000) h
theorem e24KC2PhiAboveLeaf00010 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0001) = true := by
  have h : ((childLL phiAboveCell0001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell0001) h
theorem e24KC2PhiAboveLeaf00011 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0001) = true := by
  have h : ((childLH phiAboveCell0001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell0001) h
theorem e24KC2PhiAboveLeaf00012 :
    adaptiveCoverCheck 11 (childHL phiAboveCell0001) = true := by
  have h : ((childHL phiAboveCell0001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell0001) h
theorem e24KC2PhiAboveLeaf00013 :
    adaptiveCoverCheck 11 (childHH phiAboveCell0001) = true := by
  have h : ((childHH phiAboveCell0001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell0001) h

theorem e24KC2PhiAboveLeaf0002 :
    adaptiveCoverCheck 12 phiAboveCell0002 = true := by
  have h : physicallyIrrelevant phiAboveCell0002 = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 12 phiAboveCell0002 h
theorem e24KC2PhiAboveLeaf0003 :
    adaptiveCoverCheck 12 phiAboveCell0003 = true := by
  have h : (phiAboveCell0003).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0003 h
theorem e24KC2PhiAboveLeaf00100 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0010) = true := by
  have h : ((childLL phiAboveCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell0010) h
theorem e24KC2PhiAboveLeaf00101 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0010) = true := by
  have h : ((childLH phiAboveCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell0010) h
theorem e24KC2PhiAboveLeaf00102 :
    adaptiveCoverCheck 11 (childHL phiAboveCell0010) = true := by
  have h : ((childHL phiAboveCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell0010) h
theorem e24KC2PhiAboveLeaf00103 :
    adaptiveCoverCheck 11 (childHH phiAboveCell0010) = true := by
  have h : ((childHH phiAboveCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell0010) h
theorem e24KC2PhiAboveLeaf00110 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0011) = true := by
  have h : ((childLL phiAboveCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell0011) h
theorem e24KC2PhiAboveLeaf00111 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0011) = true := by
  have h : ((childLH phiAboveCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell0011) h
theorem e24KC2PhiAboveLeaf00112 :
    adaptiveCoverCheck 11 (childHL phiAboveCell0011) = true := by
  have h : ((childHL phiAboveCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell0011) h
theorem e24KC2PhiAboveLeaf00113 :
    adaptiveCoverCheck 11 (childHH phiAboveCell0011) = true := by
  have h : ((childHH phiAboveCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell0011) h
theorem e24KC2PhiAboveLeaf0012 :
    adaptiveCoverCheck 12 phiAboveCell0012 = true := by
  have h : (phiAboveCell0012).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0012 h
theorem e24KC2PhiAboveLeaf0013 :
    adaptiveCoverCheck 12 phiAboveCell0013 = true := by
  have h : (phiAboveCell0013).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0013 h

theorem e24KC2PhiAboveLeaf002 :
    adaptiveCoverCheck 13 (childHL (childLL (childLL e24PhiAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childLL e24PhiAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL (childLL (childLL
    e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf0030 :
    adaptiveCoverCheck 12 phiAboveCell0030 = true := by
  have h : (phiAboveCell0030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0030 h
theorem e24KC2PhiAboveLeaf0031 :
    adaptiveCoverCheck 12 phiAboveCell0031 = true := by
  have h : (phiAboveCell0031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0031 h

theorem e24KC2PhiAboveLeaf0032 :
    adaptiveCoverCheck 12 phiAboveCell0032 = true := by
  have h : physicallyIrrelevant phiAboveCell0032 = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 12 phiAboveCell0032 h
theorem e24KC2PhiAboveLeaf0033 :
    adaptiveCoverCheck 12 phiAboveCell0033 = true := by
  have h : (phiAboveCell0033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0033 h
theorem e24KC2PhiAboveLeaf01000 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0100) = true := by
  have h : ((childLL phiAboveCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell0100) h
theorem e24KC2PhiAboveLeaf01001 :
    adaptiveCoverCheck 11 (childLH phiAboveCell0100) = true := by
  have h : ((childLH phiAboveCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell0100) h
theorem e24KC2PhiAboveLeaf01002 :
    adaptiveCoverCheck 11 (childHL phiAboveCell0100) = true := by
  have h : ((childHL phiAboveCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell0100) h
theorem e24KC2PhiAboveLeaf01003 :
    adaptiveCoverCheck 11 (childHH phiAboveCell0100) = true := by
  have h : ((childHH phiAboveCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell0100) h
theorem e24KC2PhiAboveLeaf01010 :
    adaptiveCoverCheck 11 (childLL phiAboveCell0101) = true := by
  have h : ((childLL phiAboveCell0101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell0101) h
theorem e24KC2PhiAboveLeaf010110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell0101)) = true := by
  have h : ((childLL (childLH phiAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH phiAboveCell0101)) h
theorem e24KC2PhiAboveLeaf010111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell0101)) = true := by
  have h : ((childLH (childLH phiAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH phiAboveCell0101)) h
theorem e24KC2PhiAboveLeaf010112 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell0101)) = true := by
  have h : ((childHL (childLH phiAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH phiAboveCell0101)) h
theorem e24KC2PhiAboveLeaf010113 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell0101)) = true := by
  have h : ((childHH (childLH phiAboveCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH phiAboveCell0101)) h
theorem e24KC2PhiAboveLeaf01012 :
    adaptiveCoverCheck 11 (childHL phiAboveCell0101) = true := by
  have h : ((childHL phiAboveCell0101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell0101) h
theorem e24KC2PhiAboveLeaf01013 :
    adaptiveCoverCheck 11 (childHH phiAboveCell0101) = true := by
  have h : ((childHH phiAboveCell0101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell0101) h
theorem e24KC2PhiAboveLeaf0102 :
    adaptiveCoverCheck 12 phiAboveCell0102 = true := by
  have h : (phiAboveCell0102).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0102 h
theorem e24KC2PhiAboveLeaf0103 :
    adaptiveCoverCheck 12 phiAboveCell0103 = true := by
  have h : (phiAboveCell0103).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0103 h
theorem e24KC2PhiAboveLeaf011000 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell0110)) = true := by
  have h : ((childLL (childLL phiAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL phiAboveCell0110)) h
theorem e24KC2PhiAboveLeaf011001 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell0110)) = true := by
  have h : ((childLH (childLL phiAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL phiAboveCell0110)) h
theorem e24KC2PhiAboveLeaf011002 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell0110)) = true := by
  have h : ((childHL (childLL phiAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL phiAboveCell0110)) h
theorem e24KC2PhiAboveLeaf011003 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell0110)) = true := by
  have h : ((childHH (childLL phiAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL phiAboveCell0110)) h
theorem e24KC2PhiAboveLeaf011010 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell0110)) = true := by
  have h : ((childLL (childLH phiAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH phiAboveCell0110)) h
theorem e24KC2PhiAboveLeaf011011 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell0110)) = true := by
  have h : ((childLH (childLH phiAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH phiAboveCell0110)) h
theorem e24KC2PhiAboveLeaf011012 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell0110)) = true := by
  have h : ((childHL (childLH phiAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH phiAboveCell0110)) h
theorem e24KC2PhiAboveLeaf011013 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell0110)) = true := by
  have h : ((childHH (childLH phiAboveCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH phiAboveCell0110)) h
theorem e24KC2PhiAboveLeaf01102 :
    adaptiveCoverCheck 11 (childHL phiAboveCell0110) = true := by
  have h : ((childHL phiAboveCell0110)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell0110) h
theorem e24KC2PhiAboveLeaf01103 :
    adaptiveCoverCheck 11 (childHH phiAboveCell0110) = true := by
  have h : ((childHH phiAboveCell0110)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell0110) h
theorem e24KC2PhiAboveLeaf011100 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell0111)) = true := by
  have h : ((childLL (childLL phiAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL phiAboveCell0111)) h
theorem e24KC2PhiAboveLeaf011101 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell0111)) = true := by
  have h : ((childLH (childLL phiAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL phiAboveCell0111)) h
theorem e24KC2PhiAboveLeaf011102 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell0111)) = true := by
  have h : ((childHL (childLL phiAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL phiAboveCell0111)) h
theorem e24KC2PhiAboveLeaf011103 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell0111)) = true := by
  have h : ((childHH (childLL phiAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL phiAboveCell0111)) h
theorem e24KC2PhiAboveLeaf011110 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell0111)) = true := by
  have h : ((childLL (childLH phiAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH phiAboveCell0111)) h
theorem e24KC2PhiAboveLeaf011111 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell0111)) = true := by
  have h : ((childLH (childLH phiAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH phiAboveCell0111)) h
theorem e24KC2PhiAboveLeaf011112 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell0111)) = true := by
  have h : ((childHL (childLH phiAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH phiAboveCell0111)) h
theorem e24KC2PhiAboveLeaf011113 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell0111)) = true := by
  have h : ((childHH (childLH phiAboveCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH phiAboveCell0111)) h
theorem e24KC2PhiAboveLeaf01112 :
    adaptiveCoverCheck 11 (childHL phiAboveCell0111) = true := by
  have h : ((childHL phiAboveCell0111)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell0111) h
theorem e24KC2PhiAboveLeaf01113 :
    adaptiveCoverCheck 11 (childHH phiAboveCell0111) = true := by
  have h : ((childHH phiAboveCell0111)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell0111) h
theorem e24KC2PhiAboveLeaf0112 :
    adaptiveCoverCheck 12 phiAboveCell0112 = true := by
  have h : (phiAboveCell0112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0112 h
theorem e24KC2PhiAboveLeaf0113 :
    adaptiveCoverCheck 12 phiAboveCell0113 = true := by
  have h : (phiAboveCell0113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0113 h
theorem e24KC2PhiAboveLeaf0120 :
    adaptiveCoverCheck 12 phiAboveCell0120 = true := by
  have h : (phiAboveCell0120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0120 h
theorem e24KC2PhiAboveLeaf0121 :
    adaptiveCoverCheck 12 phiAboveCell0121 = true := by
  have h : (phiAboveCell0121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0121 h
theorem e24KC2PhiAboveLeaf0122 :
    adaptiveCoverCheck 12 phiAboveCell0122 = true := by
  have h : (phiAboveCell0122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0122 h
theorem e24KC2PhiAboveLeaf0123 :
    adaptiveCoverCheck 12 phiAboveCell0123 = true := by
  have h : (phiAboveCell0123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0123 h
theorem e24KC2PhiAboveLeaf0130 :
    adaptiveCoverCheck 12 phiAboveCell0130 = true := by
  have h : (phiAboveCell0130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0130 h
theorem e24KC2PhiAboveLeaf0131 :
    adaptiveCoverCheck 12 phiAboveCell0131 = true := by
  have h : (phiAboveCell0131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0131 h
theorem e24KC2PhiAboveLeaf0132 :
    adaptiveCoverCheck 12 phiAboveCell0132 = true := by
  have h : (phiAboveCell0132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0132 h
theorem e24KC2PhiAboveLeaf0133 :
    adaptiveCoverCheck 12 phiAboveCell0133 = true := by
  have h : (phiAboveCell0133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell0133 h

theorem e24KC2PhiAboveLeaf02 :
    adaptiveCoverCheck 14 (childHL (childLL e24PhiAboveRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childLL e24PhiAboveRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 (childHL (childLL e24PhiAboveRoot)) h
theorem e24KC2PhiAboveLeaf030 :
    adaptiveCoverCheck 13 (childLL (childHH (childLL e24PhiAboveRoot))) = true := by
  have h : ((childLL (childHH (childLL e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childLL e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf031 :
    adaptiveCoverCheck 13 (childLH (childHH (childLL e24PhiAboveRoot))) = true := by
  have h : ((childLH (childHH (childLL e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childLL e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf032 :
    adaptiveCoverCheck 13 (childHL (childHH (childLL e24PhiAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childLL e24PhiAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL (childHH (childLL
    e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf033 :
    adaptiveCoverCheck 13 (childHH (childHH (childLL e24PhiAboveRoot))) = true := by
  have h : ((childHH (childHH (childLL e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLL e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf100000 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1000)) = true := by
  have h : ((childLL (childLL phiAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL phiAboveCell1000)) h
theorem e24KC2PhiAboveLeaf100001 :
    adaptiveCoverCheck 10 (childLH (childLL phiAboveCell1000)) = true := by
  have h : ((childLH (childLL phiAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLL phiAboveCell1000)) h
theorem e24KC2PhiAboveLeaf100002 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1000)) = true := by
  have h : ((childHL (childLL phiAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL phiAboveCell1000)) h
theorem e24KC2PhiAboveLeaf100003 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1000)) = true := by
  have h : ((childHH (childLL phiAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL phiAboveCell1000)) h
theorem e24KC2PhiAboveLeaf100010 :
    adaptiveCoverCheck 10 (childLL (childLH phiAboveCell1000)) = true := by
  have h : ((childLL (childLH phiAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLH phiAboveCell1000)) h
theorem e24KC2PhiAboveLeaf100011 :
    adaptiveCoverCheck 10 (childLH (childLH phiAboveCell1000)) = true := by
  have h : ((childLH (childLH phiAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childLH phiAboveCell1000)) h
theorem e24KC2PhiAboveLeaf100012 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1000)) = true := by
  have h : ((childHL (childLH phiAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH phiAboveCell1000)) h
theorem e24KC2PhiAboveLeaf100013 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1000)) = true := by
  have h : ((childHH (childLH phiAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH phiAboveCell1000)) h
theorem e24KC2PhiAboveLeaf10002 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1000) = true := by
  have h : ((childHL phiAboveCell1000)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1000) h
theorem e24KC2PhiAboveLeaf10003 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1000) = true := by
  have h : ((childHH phiAboveCell1000)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1000) h
theorem e24KC2PhiAboveLeaf100100 :
    adaptiveCoverCheck 10 (childLL (childLL phiAboveCell1001)) = true := by
  have h : ((childLL (childLL phiAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childLL phiAboveCell1001)) h
theorem e24KC2PhiAboveLeaf1001010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL phiAboveCell1001))) = true := by
  have h : ((childLL (childLH (childLL phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL phiAboveCell1001))) = true := by
  have h : ((childLH (childLH (childLL phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL phiAboveCell1001))) = true := by
  have h : ((childHL (childLH (childLL phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL phiAboveCell1001))) = true := by
  have h : ((childHH (childLH (childLL phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf100102 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1001)) = true := by
  have h : ((childHL (childLL phiAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL phiAboveCell1001)) h
theorem e24KC2PhiAboveLeaf100103 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1001)) = true := by
  have h : ((childHH (childLL phiAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL phiAboveCell1001)) h
theorem e24KC2PhiAboveLeaf1001100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH phiAboveCell1001))) = true := by
  have h : ((childLL (childLL (childLH phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH phiAboveCell1001))) = true := by
  have h : ((childLH (childLL (childLH phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH phiAboveCell1001))) = true := by
  have h : ((childHL (childLL (childLH phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH phiAboveCell1001))) = true := by
  have h : ((childHH (childLL (childLH phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH phiAboveCell1001))) = true := by
  have h : ((childLL (childLH (childLH phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH phiAboveCell1001))) = true := by
  have h : ((childLH (childLH (childLH phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH phiAboveCell1001))) = true := by
  have h : ((childHL (childLH (childLH phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf1001113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH phiAboveCell1001))) = true := by
  have h : ((childHH (childLH (childLH phiAboveCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH phiAboveCell1001))) h
theorem e24KC2PhiAboveLeaf100112 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1001)) = true := by
  have h : ((childHL (childLH phiAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH phiAboveCell1001)) h
theorem e24KC2PhiAboveLeaf100113 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1001)) = true := by
  have h : ((childHH (childLH phiAboveCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH phiAboveCell1001)) h
theorem e24KC2PhiAboveLeaf10012 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1001) = true := by
  have h : ((childHL phiAboveCell1001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1001) h
theorem e24KC2PhiAboveLeaf10013 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1001) = true := by
  have h : ((childHH phiAboveCell1001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1001) h
theorem e24KC2PhiAboveLeaf10020 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1002) = true := by
  have h : ((childLL phiAboveCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell1002) h
theorem e24KC2PhiAboveLeaf10021 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1002) = true := by
  have h : ((childLH phiAboveCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell1002) h
theorem e24KC2PhiAboveLeaf10022 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1002) = true := by
  have h : ((childHL phiAboveCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1002) h
theorem e24KC2PhiAboveLeaf10023 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1002) = true := by
  have h : ((childHH phiAboveCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1002) h
theorem e24KC2PhiAboveLeaf10030 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1003) = true := by
  have h : ((childLL phiAboveCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell1003) h
theorem e24KC2PhiAboveLeaf10031 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1003) = true := by
  have h : ((childLH phiAboveCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell1003) h
theorem e24KC2PhiAboveLeaf10032 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1003) = true := by
  have h : ((childHL phiAboveCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1003) h
theorem e24KC2PhiAboveLeaf10033 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1003) = true := by
  have h : ((childHH phiAboveCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1003) h
theorem e24KC2PhiAboveLeaf1010000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL phiAboveCell1010))) = true := by
  have h : ((childLL (childLL (childLL phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL phiAboveCell1010))) = true := by
  have h : ((childLH (childLL (childLL phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL phiAboveCell1010))) = true := by
  have h : ((childHL (childLL (childLL phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL phiAboveCell1010))) = true := by
  have h : ((childHH (childLL (childLL phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL phiAboveCell1010))) = true := by
  have h : ((childLL (childLH (childLL phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL phiAboveCell1010))) = true := by
  have h : ((childLH (childLH (childLL phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLL phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL phiAboveCell1010))) = true := by
  have h : ((childHL (childLH (childLL phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL phiAboveCell1010))) = true := by
  have h : ((childHH (childLH (childLL phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf101002 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1010)) = true := by
  have h : ((childHL (childLL phiAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL phiAboveCell1010)) h
theorem e24KC2PhiAboveLeaf101003 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1010)) = true := by
  have h : ((childHH (childLL phiAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL phiAboveCell1010)) h
theorem e24KC2PhiAboveLeaf1010100 :
    adaptiveCoverCheck 9 (childLL (childLL (childLH phiAboveCell1010))) = true := by
  have h : ((childLL (childLL (childLH phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLH phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010101 :
    adaptiveCoverCheck 9 (childLH (childLL (childLH phiAboveCell1010))) = true := by
  have h : ((childLH (childLL (childLH phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLH phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH phiAboveCell1010))) = true := by
  have h : ((childHL (childLL (childLH phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH phiAboveCell1010))) = true := by
  have h : ((childHH (childLL (childLH phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010110 :
    adaptiveCoverCheck 9 (childLL (childLH (childLH phiAboveCell1010))) = true := by
  have h : ((childLL (childLH (childLH phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLH phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH phiAboveCell1010))) = true := by
  have h : ((childLH (childLH (childLH phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH (childLH phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH phiAboveCell1010))) = true := by
  have h : ((childHL (childLH (childLH phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf1010113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH phiAboveCell1010))) = true := by
  have h : ((childHH (childLH (childLH phiAboveCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH phiAboveCell1010))) h
theorem e24KC2PhiAboveLeaf101012 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1010)) = true := by
  have h : ((childHL (childLH phiAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH phiAboveCell1010)) h
theorem e24KC2PhiAboveLeaf101013 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1010)) = true := by
  have h : ((childHH (childLH phiAboveCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH phiAboveCell1010)) h
theorem e24KC2PhiAboveLeaf10102 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1010) = true := by
  have h : ((childHL phiAboveCell1010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1010) h
theorem e24KC2PhiAboveLeaf10103 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1010) = true := by
  have h : ((childHH phiAboveCell1010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1010) h
theorem e24KC2PhiAboveLeaf1011000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL phiAboveCell1011))) = true := by
  have h : ((childLL (childLL (childLL phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL (childLL phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf1011001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL phiAboveCell1011))) = true := by
  have h : ((childLH (childLL (childLL phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL (childLL phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf1011002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL phiAboveCell1011))) = true := by
  have h : ((childHL (childLL (childLL phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf1011003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL phiAboveCell1011))) = true := by
  have h : ((childHH (childLL (childLL phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf1011010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL phiAboveCell1011))) = true := by
  have h : ((childLL (childLH (childLL phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH (childLL phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf1011012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL phiAboveCell1011))) = true := by
  have h : ((childHL (childLH (childLL phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf1011013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL phiAboveCell1011))) = true := by
  have h : ((childHH (childLH (childLL phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf101102 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1011)) = true := by
  have h : ((childHL (childLL phiAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL phiAboveCell1011)) h
theorem e24KC2PhiAboveLeaf101103 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1011)) = true := by
  have h : ((childHH (childLL phiAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL phiAboveCell1011)) h
theorem e24KC2PhiAboveLeaf1011102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH phiAboveCell1011))) = true := by
  have h : ((childHL (childLL (childLH phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf1011103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH phiAboveCell1011))) = true := by
  have h : ((childHH (childLL (childLH phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf1011112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH phiAboveCell1011))) = true := by
  have h : ((childHL (childLH (childLH phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf1011113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH phiAboveCell1011))) = true := by
  have h : ((childHH (childLH (childLH phiAboveCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH phiAboveCell1011))) h
theorem e24KC2PhiAboveLeaf101112 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1011)) = true := by
  have h : ((childHL (childLH phiAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH phiAboveCell1011)) h
theorem e24KC2PhiAboveLeaf101113 :
    adaptiveCoverCheck 10 (childHH (childLH phiAboveCell1011)) = true := by
  have h : ((childHH (childLH phiAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLH phiAboveCell1011)) h
theorem e24KC2PhiAboveLeaf10112 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1011) = true := by
  have h : ((childHL phiAboveCell1011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1011) h
theorem e24KC2PhiAboveLeaf101130 :
    adaptiveCoverCheck 10 (childLL (childHH phiAboveCell1011)) = true := by
  have h : ((childLL (childHH phiAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH phiAboveCell1011)) h
theorem e24KC2PhiAboveLeaf101131 :
    adaptiveCoverCheck 10 (childLH (childHH phiAboveCell1011)) = true := by
  have h : ((childLH (childHH phiAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH phiAboveCell1011)) h
theorem e24KC2PhiAboveLeaf101132 :
    adaptiveCoverCheck 10 (childHL (childHH phiAboveCell1011)) = true := by
  have h : ((childHL (childHH phiAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH phiAboveCell1011)) h
theorem e24KC2PhiAboveLeaf101133 :
    adaptiveCoverCheck 10 (childHH (childHH phiAboveCell1011)) = true := by
  have h : ((childHH (childHH phiAboveCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH phiAboveCell1011)) h
theorem e24KC2PhiAboveLeaf10120 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1012) = true := by
  have h : ((childLL phiAboveCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell1012) h
theorem e24KC2PhiAboveLeaf10121 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1012) = true := by
  have h : ((childLH phiAboveCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell1012) h
theorem e24KC2PhiAboveLeaf10122 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1012) = true := by
  have h : ((childHL phiAboveCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1012) h
theorem e24KC2PhiAboveLeaf10123 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1012) = true := by
  have h : ((childHH phiAboveCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1012) h
theorem e24KC2PhiAboveLeaf10130 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1013) = true := by
  have h : ((childLL phiAboveCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell1013) h
theorem e24KC2PhiAboveLeaf10131 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1013) = true := by
  have h : ((childLH phiAboveCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell1013) h
theorem e24KC2PhiAboveLeaf10132 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1013) = true := by
  have h : ((childHL phiAboveCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1013) h
theorem e24KC2PhiAboveLeaf10133 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1013) = true := by
  have h : ((childHH phiAboveCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1013) h
theorem e24KC2PhiAboveLeaf1020 :
    adaptiveCoverCheck 12 phiAboveCell1020 = true := by
  have h : (phiAboveCell1020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1020 h
theorem e24KC2PhiAboveLeaf1021 :
    adaptiveCoverCheck 12 phiAboveCell1021 = true := by
  have h : (phiAboveCell1021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1021 h
theorem e24KC2PhiAboveLeaf1022 :
    adaptiveCoverCheck 12 phiAboveCell1022 = true := by
  have h : (phiAboveCell1022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1022 h
theorem e24KC2PhiAboveLeaf1023 :
    adaptiveCoverCheck 12 phiAboveCell1023 = true := by
  have h : (phiAboveCell1023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1023 h
theorem e24KC2PhiAboveLeaf1030 :
    adaptiveCoverCheck 12 phiAboveCell1030 = true := by
  have h : (phiAboveCell1030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1030 h
theorem e24KC2PhiAboveLeaf1031 :
    adaptiveCoverCheck 12 phiAboveCell1031 = true := by
  have h : (phiAboveCell1031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1031 h
theorem e24KC2PhiAboveLeaf1032 :
    adaptiveCoverCheck 12 phiAboveCell1032 = true := by
  have h : (phiAboveCell1032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1032 h
theorem e24KC2PhiAboveLeaf1033 :
    adaptiveCoverCheck 12 phiAboveCell1033 = true := by
  have h : (phiAboveCell1033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1033 h
theorem e24KC2PhiAboveLeaf1100002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL phiAboveCell1100))) = true := by
  have h : ((childHL (childLL (childLL phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf1100003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL phiAboveCell1100))) = true := by
  have h : ((childHH (childLL (childLL phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf1100012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL phiAboveCell1100))) = true := by
  have h : ((childHL (childLH (childLL phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLL phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf1100013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL phiAboveCell1100))) = true := by
  have h : ((childHH (childLH (childLL phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLL phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf110002 :
    adaptiveCoverCheck 10 (childHL (childLL phiAboveCell1100)) = true := by
  have h : ((childHL (childLL phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLL phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf110003 :
    adaptiveCoverCheck 10 (childHH (childLL phiAboveCell1100)) = true := by
  have h : ((childHH (childLL phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childLL phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf1100102 :
    adaptiveCoverCheck 9 (childHL (childLL (childLH phiAboveCell1100))) = true := by
  have h : ((childHL (childLL (childLH phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLH phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf1100103 :
    adaptiveCoverCheck 9 (childHH (childLL (childLH phiAboveCell1100))) = true := by
  have h : ((childHH (childLL (childLH phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLH phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf1100112 :
    adaptiveCoverCheck 9 (childHL (childLH (childLH phiAboveCell1100))) = true := by
  have h : ((childHL (childLH (childLH phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH (childLH phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf1100113 :
    adaptiveCoverCheck 9 (childHH (childLH (childLH phiAboveCell1100))) = true := by
  have h : ((childHH (childLH (childLH phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH (childLH phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf110012 :
    adaptiveCoverCheck 10 (childHL (childLH phiAboveCell1100)) = true := by
  have h : ((childHL (childLH phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childLH phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf1100130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH phiAboveCell1100))) = true := by
  have h : ((childLL (childHH (childLH phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf1100131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH phiAboveCell1100))) = true := by
  have h : ((childLH (childHH (childLH phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf1100132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH phiAboveCell1100))) = true := by
  have h : ((childHL (childHH (childLH phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf1100133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH phiAboveCell1100))) = true := by
  have h : ((childHH (childHH (childLH phiAboveCell1100)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH phiAboveCell1100))) h
theorem e24KC2PhiAboveLeaf110020 :
    adaptiveCoverCheck 10 (childLL (childHL phiAboveCell1100)) = true := by
  have h : ((childLL (childHL phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf110021 :
    adaptiveCoverCheck 10 (childLH (childHL phiAboveCell1100)) = true := by
  have h : ((childLH (childHL phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf110022 :
    adaptiveCoverCheck 10 (childHL (childHL phiAboveCell1100)) = true := by
  have h : ((childHL (childHL phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf110023 :
    adaptiveCoverCheck 10 (childHH (childHL phiAboveCell1100)) = true := by
  have h : ((childHH (childHL phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf110030 :
    adaptiveCoverCheck 10 (childLL (childHH phiAboveCell1100)) = true := by
  have h : ((childLL (childHH phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf110031 :
    adaptiveCoverCheck 10 (childLH (childHH phiAboveCell1100)) = true := by
  have h : ((childLH (childHH phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf110032 :
    adaptiveCoverCheck 10 (childHL (childHH phiAboveCell1100)) = true := by
  have h : ((childHL (childHH phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf110033 :
    adaptiveCoverCheck 10 (childHH (childHH phiAboveCell1100)) = true := by
  have h : ((childHH (childHH phiAboveCell1100))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH phiAboveCell1100)) h
theorem e24KC2PhiAboveLeaf1101002 :
    adaptiveCoverCheck 9 (childHL (childLL (childLL phiAboveCell1101))) = true := by
  have h : ((childHL (childLL (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101003 :
    adaptiveCoverCheck 9 (childHH (childLL (childLL phiAboveCell1101))) = true := by
  have h : ((childHH (childLL (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL phiAboveCell1101))) = true := by
  have h : ((childLL (childHL (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL phiAboveCell1101))) = true := by
  have h : ((childLH (childHL (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL phiAboveCell1101))) = true := by
  have h : ((childHL (childHL (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL phiAboveCell1101))) = true := by
  have h : ((childHH (childHL (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL phiAboveCell1101))) = true := by
  have h : ((childLL (childHH (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL phiAboveCell1101))) = true := by
  have h : ((childLH (childHH (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL phiAboveCell1101))) = true := by
  have h : ((childHL (childHH (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL phiAboveCell1101))) = true := by
  have h : ((childHH (childHH (childLL phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH phiAboveCell1101))) = true := by
  have h : ((childLL (childHL (childLH phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH phiAboveCell1101))) = true := by
  have h : ((childLH (childHL (childLH phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH phiAboveCell1101))) = true := by
  have h : ((childHL (childHL (childLH phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH phiAboveCell1101))) = true := by
  have h : ((childHH (childHL (childLH phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH phiAboveCell1101))) = true := by
  have h : ((childLL (childHH (childLH phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH phiAboveCell1101))) = true := by
  have h : ((childLH (childHH (childLH phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH phiAboveCell1101))) = true := by
  have h : ((childHL (childHH (childLH phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf1101133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH phiAboveCell1101))) = true := by
  have h : ((childHH (childHH (childLH phiAboveCell1101)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH phiAboveCell1101))) h
theorem e24KC2PhiAboveLeaf110120 :
    adaptiveCoverCheck 10 (childLL (childHL phiAboveCell1101)) = true := by
  have h : ((childLL (childHL phiAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL phiAboveCell1101)) h
theorem e24KC2PhiAboveLeaf110121 :
    adaptiveCoverCheck 10 (childLH (childHL phiAboveCell1101)) = true := by
  have h : ((childLH (childHL phiAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL phiAboveCell1101)) h
theorem e24KC2PhiAboveLeaf110122 :
    adaptiveCoverCheck 10 (childHL (childHL phiAboveCell1101)) = true := by
  have h : ((childHL (childHL phiAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL phiAboveCell1101)) h
theorem e24KC2PhiAboveLeaf110123 :
    adaptiveCoverCheck 10 (childHH (childHL phiAboveCell1101)) = true := by
  have h : ((childHH (childHL phiAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL phiAboveCell1101)) h
theorem e24KC2PhiAboveLeaf110130 :
    adaptiveCoverCheck 10 (childLL (childHH phiAboveCell1101)) = true := by
  have h : ((childLL (childHH phiAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH phiAboveCell1101)) h
theorem e24KC2PhiAboveLeaf110131 :
    adaptiveCoverCheck 10 (childLH (childHH phiAboveCell1101)) = true := by
  have h : ((childLH (childHH phiAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH phiAboveCell1101)) h
theorem e24KC2PhiAboveLeaf110132 :
    adaptiveCoverCheck 10 (childHL (childHH phiAboveCell1101)) = true := by
  have h : ((childHL (childHH phiAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH phiAboveCell1101)) h
theorem e24KC2PhiAboveLeaf110133 :
    adaptiveCoverCheck 10 (childHH (childHH phiAboveCell1101)) = true := by
  have h : ((childHH (childHH phiAboveCell1101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH phiAboveCell1101)) h
theorem e24KC2PhiAboveLeaf11020 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1102) = true := by
  have h : ((childLL phiAboveCell1102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell1102) h
theorem e24KC2PhiAboveLeaf11021 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1102) = true := by
  have h : ((childLH phiAboveCell1102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell1102) h
theorem e24KC2PhiAboveLeaf11022 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1102) = true := by
  have h : ((childHL phiAboveCell1102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1102) h
theorem e24KC2PhiAboveLeaf11023 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1102) = true := by
  have h : ((childHH phiAboveCell1102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1102) h
theorem e24KC2PhiAboveLeaf11030 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1103) = true := by
  have h : ((childLL phiAboveCell1103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell1103) h
theorem e24KC2PhiAboveLeaf11031 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1103) = true := by
  have h : ((childLH phiAboveCell1103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell1103) h
theorem e24KC2PhiAboveLeaf11032 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1103) = true := by
  have h : ((childHL phiAboveCell1103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1103) h
theorem e24KC2PhiAboveLeaf11033 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1103) = true := by
  have h : ((childHH phiAboveCell1103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1103) h
theorem e24KC2PhiAboveLeaf1110020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL phiAboveCell1110))) = true := by
  have h : ((childLL (childHL (childLL phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL phiAboveCell1110))) = true := by
  have h : ((childLH (childHL (childLL phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL phiAboveCell1110))) = true := by
  have h : ((childHL (childHL (childLL phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL phiAboveCell1110))) = true := by
  have h : ((childHH (childHL (childLL phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL phiAboveCell1110))) = true := by
  have h : ((childLL (childHH (childLL phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL phiAboveCell1110))) = true := by
  have h : ((childLH (childHH (childLL phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL phiAboveCell1110))) = true := by
  have h : ((childHL (childHH (childLL phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL phiAboveCell1110))) = true := by
  have h : ((childHH (childHH (childLL phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH phiAboveCell1110))) = true := by
  have h : ((childLL (childHL (childLH phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH phiAboveCell1110))) = true := by
  have h : ((childLH (childHL (childLH phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH phiAboveCell1110))) = true := by
  have h : ((childHL (childHL (childLH phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH phiAboveCell1110))) = true := by
  have h : ((childHH (childHL (childLH phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH phiAboveCell1110))) = true := by
  have h : ((childLL (childHH (childLH phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110131 :
    adaptiveCoverCheck 9 (childLH (childHH (childLH phiAboveCell1110))) = true := by
  have h : ((childLH (childHH (childLH phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLH phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH phiAboveCell1110))) = true := by
  have h : ((childHL (childHH (childLH phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf1110133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH phiAboveCell1110))) = true := by
  have h : ((childHH (childHH (childLH phiAboveCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH phiAboveCell1110))) h
theorem e24KC2PhiAboveLeaf111020 :
    adaptiveCoverCheck 10 (childLL (childHL phiAboveCell1110)) = true := by
  have h : ((childLL (childHL phiAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL phiAboveCell1110)) h
theorem e24KC2PhiAboveLeaf111021 :
    adaptiveCoverCheck 10 (childLH (childHL phiAboveCell1110)) = true := by
  have h : ((childLH (childHL phiAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL phiAboveCell1110)) h
theorem e24KC2PhiAboveLeaf111022 :
    adaptiveCoverCheck 10 (childHL (childHL phiAboveCell1110)) = true := by
  have h : ((childHL (childHL phiAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL phiAboveCell1110)) h
theorem e24KC2PhiAboveLeaf111023 :
    adaptiveCoverCheck 10 (childHH (childHL phiAboveCell1110)) = true := by
  have h : ((childHH (childHL phiAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL phiAboveCell1110)) h
theorem e24KC2PhiAboveLeaf111030 :
    adaptiveCoverCheck 10 (childLL (childHH phiAboveCell1110)) = true := by
  have h : ((childLL (childHH phiAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH phiAboveCell1110)) h
theorem e24KC2PhiAboveLeaf111031 :
    adaptiveCoverCheck 10 (childLH (childHH phiAboveCell1110)) = true := by
  have h : ((childLH (childHH phiAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH phiAboveCell1110)) h
theorem e24KC2PhiAboveLeaf111032 :
    adaptiveCoverCheck 10 (childHL (childHH phiAboveCell1110)) = true := by
  have h : ((childHL (childHH phiAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH phiAboveCell1110)) h
theorem e24KC2PhiAboveLeaf111033 :
    adaptiveCoverCheck 10 (childHH (childHH phiAboveCell1110)) = true := by
  have h : ((childHH (childHH phiAboveCell1110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH phiAboveCell1110)) h
theorem e24KC2PhiAboveLeaf1111020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL phiAboveCell1111))) = true := by
  have h : ((childLL (childHL (childLL phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111021 :
    adaptiveCoverCheck 9 (childLH (childHL (childLL phiAboveCell1111))) = true := by
  have h : ((childLH (childHL (childLL phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLL phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111022 :
    adaptiveCoverCheck 9 (childHL (childHL (childLL phiAboveCell1111))) = true := by
  have h : ((childHL (childHL (childLL phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLL phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111023 :
    adaptiveCoverCheck 9 (childHH (childHL (childLL phiAboveCell1111))) = true := by
  have h : ((childHH (childHL (childLL phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLL phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111030 :
    adaptiveCoverCheck 9 (childLL (childHH (childLL phiAboveCell1111))) = true := by
  have h : ((childLL (childHH (childLL phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLL phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111031 :
    adaptiveCoverCheck 9 (childLH (childHH (childLL phiAboveCell1111))) = true := by
  have h : ((childLH (childHH (childLL phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH (childLL phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111032 :
    adaptiveCoverCheck 9 (childHL (childHH (childLL phiAboveCell1111))) = true := by
  have h : ((childHL (childHH (childLL phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLL phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111033 :
    adaptiveCoverCheck 9 (childHH (childHH (childLL phiAboveCell1111))) = true := by
  have h : ((childHH (childHH (childLL phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLL phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111120 :
    adaptiveCoverCheck 9 (childLL (childHL (childLH phiAboveCell1111))) = true := by
  have h : ((childLL (childHL (childLH phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLH phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111121 :
    adaptiveCoverCheck 9 (childLH (childHL (childLH phiAboveCell1111))) = true := by
  have h : ((childLH (childHL (childLH phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL (childLH phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111122 :
    adaptiveCoverCheck 9 (childHL (childHL (childLH phiAboveCell1111))) = true := by
  have h : ((childHL (childHL (childLH phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL (childLH phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111123 :
    adaptiveCoverCheck 9 (childHH (childHL (childLH phiAboveCell1111))) = true := by
  have h : ((childHH (childHL (childLH phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL (childLH phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111130 :
    adaptiveCoverCheck 9 (childLL (childHH (childLH phiAboveCell1111))) = true := by
  have h : ((childLL (childHH (childLH phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH (childLH phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111132 :
    adaptiveCoverCheck 9 (childHL (childHH (childLH phiAboveCell1111))) = true := by
  have h : ((childHL (childHH (childLH phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH (childLH phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf1111133 :
    adaptiveCoverCheck 9 (childHH (childHH (childLH phiAboveCell1111))) = true := by
  have h : ((childHH (childHH (childLH phiAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH (childLH phiAboveCell1111))) h
theorem e24KC2PhiAboveLeaf111120 :
    adaptiveCoverCheck 10 (childLL (childHL phiAboveCell1111)) = true := by
  have h : ((childLL (childHL phiAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHL phiAboveCell1111)) h
theorem e24KC2PhiAboveLeaf111121 :
    adaptiveCoverCheck 10 (childLH (childHL phiAboveCell1111)) = true := by
  have h : ((childLH (childHL phiAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHL phiAboveCell1111)) h
theorem e24KC2PhiAboveLeaf111122 :
    adaptiveCoverCheck 10 (childHL (childHL phiAboveCell1111)) = true := by
  have h : ((childHL (childHL phiAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHL phiAboveCell1111)) h
theorem e24KC2PhiAboveLeaf111123 :
    adaptiveCoverCheck 10 (childHH (childHL phiAboveCell1111)) = true := by
  have h : ((childHH (childHL phiAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHL phiAboveCell1111)) h
theorem e24KC2PhiAboveLeaf111130 :
    adaptiveCoverCheck 10 (childLL (childHH phiAboveCell1111)) = true := by
  have h : ((childLL (childHH phiAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL (childHH phiAboveCell1111)) h
theorem e24KC2PhiAboveLeaf111131 :
    adaptiveCoverCheck 10 (childLH (childHH phiAboveCell1111)) = true := by
  have h : ((childLH (childHH phiAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH (childHH phiAboveCell1111)) h
theorem e24KC2PhiAboveLeaf111132 :
    adaptiveCoverCheck 10 (childHL (childHH phiAboveCell1111)) = true := by
  have h : ((childHL (childHH phiAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL (childHH phiAboveCell1111)) h
theorem e24KC2PhiAboveLeaf111133 :
    adaptiveCoverCheck 10 (childHH (childHH phiAboveCell1111)) = true := by
  have h : ((childHH (childHH phiAboveCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH (childHH phiAboveCell1111)) h
theorem e24KC2PhiAboveLeaf11120 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1112) = true := by
  have h : ((childLL phiAboveCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell1112) h
theorem e24KC2PhiAboveLeaf11121 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1112) = true := by
  have h : ((childLH phiAboveCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell1112) h
theorem e24KC2PhiAboveLeaf11122 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1112) = true := by
  have h : ((childHL phiAboveCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1112) h
theorem e24KC2PhiAboveLeaf11123 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1112) = true := by
  have h : ((childHH phiAboveCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1112) h
theorem e24KC2PhiAboveLeaf11130 :
    adaptiveCoverCheck 11 (childLL phiAboveCell1113) = true := by
  have h : ((childLL phiAboveCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL phiAboveCell1113) h
theorem e24KC2PhiAboveLeaf11131 :
    adaptiveCoverCheck 11 (childLH phiAboveCell1113) = true := by
  have h : ((childLH phiAboveCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH phiAboveCell1113) h
theorem e24KC2PhiAboveLeaf11132 :
    adaptiveCoverCheck 11 (childHL phiAboveCell1113) = true := by
  have h : ((childHL phiAboveCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL phiAboveCell1113) h
theorem e24KC2PhiAboveLeaf11133 :
    adaptiveCoverCheck 11 (childHH phiAboveCell1113) = true := by
  have h : ((childHH phiAboveCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH phiAboveCell1113) h
theorem e24KC2PhiAboveLeaf1120 :
    adaptiveCoverCheck 12 phiAboveCell1120 = true := by
  have h : (phiAboveCell1120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1120 h
theorem e24KC2PhiAboveLeaf1121 :
    adaptiveCoverCheck 12 phiAboveCell1121 = true := by
  have h : (phiAboveCell1121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1121 h
theorem e24KC2PhiAboveLeaf1122 :
    adaptiveCoverCheck 12 phiAboveCell1122 = true := by
  have h : (phiAboveCell1122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1122 h
theorem e24KC2PhiAboveLeaf1123 :
    adaptiveCoverCheck 12 phiAboveCell1123 = true := by
  have h : (phiAboveCell1123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1123 h
theorem e24KC2PhiAboveLeaf1130 :
    adaptiveCoverCheck 12 phiAboveCell1130 = true := by
  have h : (phiAboveCell1130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1130 h
theorem e24KC2PhiAboveLeaf1131 :
    adaptiveCoverCheck 12 phiAboveCell1131 = true := by
  have h : (phiAboveCell1131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1131 h
theorem e24KC2PhiAboveLeaf1132 :
    adaptiveCoverCheck 12 phiAboveCell1132 = true := by
  have h : (phiAboveCell1132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1132 h
theorem e24KC2PhiAboveLeaf1133 :
    adaptiveCoverCheck 12 phiAboveCell1133 = true := by
  have h : (phiAboveCell1133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 phiAboveCell1133 h
theorem e24KC2PhiAboveLeaf120 :
    adaptiveCoverCheck 13 (childLL (childHL (childLH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childHL (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHL (childLH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf121 :
    adaptiveCoverCheck 13 (childLH (childHL (childLH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childHL (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHL (childLH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf122 :
    adaptiveCoverCheck 13 (childHL (childHL (childLH e24PhiAboveRoot))) = true := by
  have h : ((childHL (childHL (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHL (childLH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf123 :
    adaptiveCoverCheck 13 (childHH (childHL (childLH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childHL (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHL (childLH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf130 :
    adaptiveCoverCheck 13 (childLL (childHH (childLH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childHH (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childLH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf131 :
    adaptiveCoverCheck 13 (childLH (childHH (childLH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childHH (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childLH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf132 :
    adaptiveCoverCheck 13 (childHL (childHH (childLH e24PhiAboveRoot))) = true := by
  have h : ((childHL (childHH (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childHH (childLH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf133 :
    adaptiveCoverCheck 13 (childHH (childHH (childLH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childHH (childLH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childLH e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf2 :
    adaptiveCoverCheck 15 (childHL e24PhiAboveRoot) = true := by
  have h : physicallyIrrelevant (childHL e24PhiAboveRoot) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL e24PhiAboveRoot) h
theorem e24KC2PhiAboveLeaf300 :
    adaptiveCoverCheck 13 (childLL (childLL (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childLL (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL (childHH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf301 :
    adaptiveCoverCheck 13 (childLH (childLL (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childLL (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL (childHH e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf302 :
    adaptiveCoverCheck 13 (childHL (childLL (childHH e24PhiAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childHH e24PhiAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL (childLL (childHH
    e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf303 :
    adaptiveCoverCheck 13 (childHH (childLL (childHH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childLL (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL (childHH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf310 :
    adaptiveCoverCheck 13 (childLL (childLH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childLH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH (childHH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf311 :
    adaptiveCoverCheck 13 (childLH (childLH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childLH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH (childHH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf312 :
    adaptiveCoverCheck 13 (childHL (childLH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childHL (childLH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH (childHH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf313 :
    adaptiveCoverCheck 13 (childHH (childLH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childLH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH (childHH e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf32 :
    adaptiveCoverCheck 14 (childHL (childHH e24PhiAboveRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childHH e24PhiAboveRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 (childHL (childHH e24PhiAboveRoot)) h
theorem e24KC2PhiAboveLeaf330 :
    adaptiveCoverCheck 13 (childLL (childHH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLL (childHH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childHH (childHH e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf331 :
    adaptiveCoverCheck 13 (childLH (childHH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childLH (childHH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childHH (childHH e24PhiAboveRoot))) h

theorem e24KC2PhiAboveLeaf332 :
    adaptiveCoverCheck 13 (childHL (childHH (childHH e24PhiAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childHH e24PhiAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL (childHH (childHH
    e24PhiAboveRoot))) h
theorem e24KC2PhiAboveLeaf333 :
    adaptiveCoverCheck 13 (childHH (childHH (childHH e24PhiAboveRoot))) = true := by
  have h : ((childHH (childHH (childHH e24PhiAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childHH (childHH e24PhiAboveRoot))) h
theorem e24KC2PhiBelowLeaf32212 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3221) = true := by
  have h : ((childHL phiBelowCell3221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3221) h
theorem e24KC2PhiBelowLeaf32220 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3222) = true := by
  have h : ((childLL phiBelowCell3222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3222) h
theorem e24KC2PhiBelowLeaf32221 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3222) = true := by
  have h : ((childLH phiBelowCell3222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3222) h
theorem e24KC2PhiBelowLeaf32222 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3222) = true := by
  have h : ((childHL phiBelowCell3222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3222) h
theorem e24KC2PhiBelowLeaf32223 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3222) = true := by
  have h : ((childHH phiBelowCell3222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3222) h
theorem e24KC2PhiBelowLeaf32230 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3223) = true := by
  have h : ((childLL phiBelowCell3223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3223) h
theorem e24KC2PhiBelowLeaf32232 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3223) = true := by
  have h : ((childHL phiBelowCell3223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3223) h
theorem e24KC2PhiBelowLeaf32233 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3223) = true := by
  have h : ((childHH phiBelowCell3223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3223) h
theorem e24KC2PhiBelowLeaf33100 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3310) = true := by
  have h : ((childLL phiBelowCell3310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3310) h
theorem e24KC2PhiBelowLeaf33101 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3310) = true := by
  have h : ((childLH phiBelowCell3310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3310) h
theorem e24KC2PhiBelowLeaf33103 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3310) = true := by
  have h : ((childHH phiBelowCell3310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3310) h
theorem e24KC2PhiBelowLeaf33110 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3311) = true := by
  have h : ((childLL phiBelowCell3311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3311) h
theorem e24KC2PhiBelowLeaf33111 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3311) = true := by
  have h : ((childLH phiBelowCell3311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3311) h
theorem e24KC2PhiBelowLeaf33112 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3311) = true := by
  have h : ((childHL phiBelowCell3311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3311) h
theorem e24KC2PhiBelowLeaf33113 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3311) = true := by
  have h : ((childHH phiBelowCell3311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3311) h
theorem e24KC2PhiBelowLeaf33130 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3313) = true := by
  have h : ((childLL phiBelowCell3313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3313) h
theorem e24KC2PhiBelowLeaf33131 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3313) = true := by
  have h : ((childLH phiBelowCell3313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3313) h
theorem e24KC2PhiBelowLeaf33133 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3313) = true := by
  have h : ((childHH phiBelowCell3313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3313) h
theorem e24KC2ThetaAboveLeaf000000 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell0000)) = true := by
  have h : ((childLL (childLL thetaAboveCell0000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell0000)) h
theorem e24KC2ThetaAboveLeaf000001 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell0000)) = true := by
  have h : ((childLH (childLL thetaAboveCell0000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell0000)) h
theorem e24KC2ThetaAboveLeaf000002 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0000)) = true := by
  have h : ((childHL (childLL thetaAboveCell0000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0000)) h
theorem e24KC2ThetaAboveLeaf000003 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0000)) = true := by
  have h : ((childHH (childLL thetaAboveCell0000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0000)) h
theorem e24KC2ThetaAboveLeaf000010 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell0000)) = true := by
  have h : ((childLL (childLH thetaAboveCell0000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell0000)) h
theorem e24KC2ThetaAboveLeaf000011 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell0000)) = true := by
  have h : ((childLH (childLH thetaAboveCell0000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell0000)) h
theorem e24KC2ThetaAboveLeaf000012 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0000)) = true := by
  have h : ((childHL (childLH thetaAboveCell0000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0000)) h
theorem e24KC2ThetaAboveLeaf000013 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0000)) = true := by
  have h : ((childHH (childLH thetaAboveCell0000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0000)) h
theorem e24KC2ThetaAboveLeaf0000200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell0000))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell0000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell0000))) h
theorem e24KC2ThetaAboveLeaf0000201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell0000))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell0000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell0000))) h
theorem e24KC2ThetaAboveLeaf00002020 :
    adaptiveCoverCheck 11 thetaAboveCell00002020 = true := by
  have h : (thetaAboveCell00002020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002020 h
theorem e24KC2ThetaAboveLeaf00002021 :
    adaptiveCoverCheck 11 thetaAboveCell00002021 = true := by
  have h : (thetaAboveCell00002021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002021 h
theorem e24KC2ThetaAboveLeaf000020220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002022) = true := by
  have h : ((childLL thetaAboveCell00002022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002022) h
theorem e24KC2ThetaAboveLeaf000020221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002022) = true := by
  have h : ((childLH thetaAboveCell00002022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002022) h
theorem e24KC2ThetaAboveLeaf000020222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002022) = true := by
  have h : ((childHL thetaAboveCell00002022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002022) h
theorem e24KC2ThetaAboveLeaf000020223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002022) = true := by
  have h : ((childHH thetaAboveCell00002022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002022) h
theorem e24KC2ThetaAboveLeaf000020230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002023) = true := by
  have h : ((childLL thetaAboveCell00002023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002023) h
theorem e24KC2ThetaAboveLeaf000020231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002023) = true := by
  have h : ((childLH thetaAboveCell00002023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002023) h
theorem e24KC2ThetaAboveLeaf000020232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002023) = true := by
  have h : ((childHL thetaAboveCell00002023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002023) h
theorem e24KC2ThetaAboveLeaf000020233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002023) = true := by
  have h : ((childHH thetaAboveCell00002023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002023) h
theorem e24KC2ThetaAboveLeaf00002030 :
    adaptiveCoverCheck 11 thetaAboveCell00002030 = true := by
  have h : (thetaAboveCell00002030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002030 h
theorem e24KC2ThetaAboveLeaf00002031 :
    adaptiveCoverCheck 11 thetaAboveCell00002031 = true := by
  have h : (thetaAboveCell00002031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002031 h
theorem e24KC2ThetaAboveLeaf000020320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002032) = true := by
  have h : ((childLL thetaAboveCell00002032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002032) h
theorem e24KC2ThetaAboveLeaf000020321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002032) = true := by
  have h : ((childLH thetaAboveCell00002032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002032) h
theorem e24KC2ThetaAboveLeaf000020322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002032) = true := by
  have h : ((childHL thetaAboveCell00002032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002032) h
theorem e24KC2ThetaAboveLeaf000020323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002032) = true := by
  have h : ((childHH thetaAboveCell00002032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002032) h
theorem e24KC2ThetaAboveLeaf000020330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002033) = true := by
  have h : ((childLL thetaAboveCell00002033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002033) h
theorem e24KC2ThetaAboveLeaf000020331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002033) = true := by
  have h : ((childLH thetaAboveCell00002033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002033) h
theorem e24KC2ThetaAboveLeaf000020332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002033) = true := by
  have h : ((childHL thetaAboveCell00002033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002033) h
theorem e24KC2ThetaAboveLeaf000020333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002033) = true := by
  have h : ((childHH thetaAboveCell00002033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002033) h
theorem e24KC2ThetaAboveLeaf0000210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell0000))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell0000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell0000))) h
theorem e24KC2ThetaAboveLeaf0000211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell0000))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell0000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell0000))) h
theorem e24KC2ThetaAboveLeaf00002120 :
    adaptiveCoverCheck 11 thetaAboveCell00002120 = true := by
  have h : (thetaAboveCell00002120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002120 h
theorem e24KC2ThetaAboveLeaf00002121 :
    adaptiveCoverCheck 11 thetaAboveCell00002121 = true := by
  have h : (thetaAboveCell00002121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002121 h
theorem e24KC2ThetaAboveLeaf000021220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002122) = true := by
  have h : ((childLL thetaAboveCell00002122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002122) h
theorem e24KC2ThetaAboveLeaf000021221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002122) = true := by
  have h : ((childLH thetaAboveCell00002122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002122) h
theorem e24KC2ThetaAboveLeaf000021222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002122) = true := by
  have h : ((childHL thetaAboveCell00002122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002122) h
theorem e24KC2ThetaAboveLeaf000021223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002122) = true := by
  have h : ((childHH thetaAboveCell00002122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002122) h
theorem e24KC2ThetaAboveLeaf000021230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002123) = true := by
  have h : ((childLL thetaAboveCell00002123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002123) h
theorem e24KC2ThetaAboveLeaf000021231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002123) = true := by
  have h : ((childLH thetaAboveCell00002123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002123) h
theorem e24KC2ThetaAboveLeaf000021232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002123) = true := by
  have h : ((childHL thetaAboveCell00002123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002123) h
theorem e24KC2ThetaAboveLeaf000021233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002123) = true := by
  have h : ((childHH thetaAboveCell00002123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002123) h
theorem e24KC2ThetaAboveLeaf00002130 :
    adaptiveCoverCheck 11 thetaAboveCell00002130 = true := by
  have h : (thetaAboveCell00002130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002130 h
theorem e24KC2ThetaAboveLeaf00002131 :
    adaptiveCoverCheck 11 thetaAboveCell00002131 = true := by
  have h : (thetaAboveCell00002131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002131 h
theorem e24KC2ThetaAboveLeaf000021320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002132) = true := by
  have h : ((childLL thetaAboveCell00002132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002132) h
theorem e24KC2ThetaAboveLeaf000021321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002132) = true := by
  have h : ((childLH thetaAboveCell00002132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002132) h
theorem e24KC2ThetaAboveLeaf000021322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002132) = true := by
  have h : ((childHL thetaAboveCell00002132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002132) h
theorem e24KC2ThetaAboveLeaf000021323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002132) = true := by
  have h : ((childHH thetaAboveCell00002132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002132) h
theorem e24KC2ThetaAboveLeaf000021330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002133) = true := by
  have h : ((childLL thetaAboveCell00002133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002133) h
theorem e24KC2ThetaAboveLeaf000021331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002133) = true := by
  have h : ((childLH thetaAboveCell00002133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002133) h
theorem e24KC2ThetaAboveLeaf000021332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002133) = true := by
  have h : ((childHL thetaAboveCell00002133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002133) h
theorem e24KC2ThetaAboveLeaf000021333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002133) = true := by
  have h : ((childHH thetaAboveCell00002133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002133) h
theorem e24KC2ThetaAboveLeaf0000220000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002200)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002200)) h
theorem e24KC2ThetaAboveLeaf0000220001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002200)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002200)) h
theorem e24KC2ThetaAboveLeaf0000220010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002200)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002200)) h
theorem e24KC2ThetaAboveLeaf0000220011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002200)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002200))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002200)) h
theorem e24KC2ThetaAboveLeaf0000220100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002201)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002201)) h
theorem e24KC2ThetaAboveLeaf0000220101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002201)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002201)) h
theorem e24KC2ThetaAboveLeaf0000220110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002201)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002201)) h
theorem e24KC2ThetaAboveLeaf0000220111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002201)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002201))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002201)) h
theorem e24KC2ThetaAboveLeaf000022020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002202) = true := by
  have h : ((childLL thetaAboveCell00002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002202) h
theorem e24KC2ThetaAboveLeaf000022021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002202) = true := by
  have h : ((childLH thetaAboveCell00002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002202) h
theorem e24KC2ThetaAboveLeaf000022022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002202) = true := by
  have h : ((childHL thetaAboveCell00002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002202) h
theorem e24KC2ThetaAboveLeaf000022023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002202) = true := by
  have h : ((childHH thetaAboveCell00002202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002202) h
theorem e24KC2ThetaAboveLeaf000022030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002203) = true := by
  have h : ((childLL thetaAboveCell00002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002203) h
theorem e24KC2ThetaAboveLeaf000022031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002203) = true := by
  have h : ((childLH thetaAboveCell00002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002203) h
theorem e24KC2ThetaAboveLeaf000022032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002203) = true := by
  have h : ((childHL thetaAboveCell00002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002203) h
theorem e24KC2ThetaAboveLeaf000022033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002203) = true := by
  have h : ((childHH thetaAboveCell00002203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002203) h
theorem e24KC2ThetaAboveLeaf0000221000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002210)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002210)) h
theorem e24KC2ThetaAboveLeaf0000221001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002210)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002210)) h
theorem e24KC2ThetaAboveLeaf0000221010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002210)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002210)) h
theorem e24KC2ThetaAboveLeaf0000221011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002210)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002210))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002210)) h
theorem e24KC2ThetaAboveLeaf0000221100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002211)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002211)) h
theorem e24KC2ThetaAboveLeaf0000221101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002211)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002211)) h
theorem e24KC2ThetaAboveLeaf0000221110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002211)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002211)) h
theorem e24KC2ThetaAboveLeaf0000221111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002211)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002211))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002211)) h
theorem e24KC2ThetaAboveLeaf000022120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002212) = true := by
  have h : ((childLL thetaAboveCell00002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002212) h
theorem e24KC2ThetaAboveLeaf000022121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00002212) = true := by
  have h : ((childLH thetaAboveCell00002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00002212) h
theorem e24KC2ThetaAboveLeaf000022122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002212) = true := by
  have h : ((childHL thetaAboveCell00002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002212) h
theorem e24KC2ThetaAboveLeaf000022123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002212) = true := by
  have h : ((childHH thetaAboveCell00002212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002212) h
theorem e24KC2ThetaAboveLeaf000022130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00002213) = true := by
  have h : ((childLL thetaAboveCell00002213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00002213) h
theorem e24KC2ThetaAboveLeaf0000221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002213)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002213)) h
theorem e24KC2ThetaAboveLeaf0000221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002213)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002213)) h
theorem e24KC2ThetaAboveLeaf0000221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002213)) = true := by
  have h : ((childHL (childLH thetaAboveCell00002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00002213)) h
theorem e24KC2ThetaAboveLeaf0000221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002213)) = true := by
  have h : ((childHH (childLH thetaAboveCell00002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00002213)) h
theorem e24KC2ThetaAboveLeaf000022132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002213) = true := by
  have h : ((childHL thetaAboveCell00002213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002213) h
theorem e24KC2ThetaAboveLeaf000022133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002213) = true := by
  have h : ((childHH thetaAboveCell00002213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002213) h
theorem e24KC2ThetaAboveLeaf00002220 :
    adaptiveCoverCheck 11 thetaAboveCell00002220 = true := by
  have h : (thetaAboveCell00002220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002220 h
theorem e24KC2ThetaAboveLeaf00002221 :
    adaptiveCoverCheck 11 thetaAboveCell00002221 = true := by
  have h : (thetaAboveCell00002221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002221 h
theorem e24KC2ThetaAboveLeaf00002222 :
    adaptiveCoverCheck 11 thetaAboveCell00002222 = true := by
  have h : (thetaAboveCell00002222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002222 h
theorem e24KC2ThetaAboveLeaf00002223 :
    adaptiveCoverCheck 11 thetaAboveCell00002223 = true := by
  have h : (thetaAboveCell00002223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002223 h
theorem e24KC2ThetaAboveLeaf00002230 :
    adaptiveCoverCheck 11 thetaAboveCell00002230 = true := by
  have h : (thetaAboveCell00002230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002230 h
theorem e24KC2ThetaAboveLeaf00002231 :
    adaptiveCoverCheck 11 thetaAboveCell00002231 = true := by
  have h : (thetaAboveCell00002231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002231 h
theorem e24KC2ThetaAboveLeaf00002232 :
    adaptiveCoverCheck 11 thetaAboveCell00002232 = true := by
  have h : (thetaAboveCell00002232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002232 h
theorem e24KC2ThetaAboveLeaf00002233 :
    adaptiveCoverCheck 11 thetaAboveCell00002233 = true := by
  have h : (thetaAboveCell00002233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002233 h
theorem e24KC2ThetaAboveLeaf0000230000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002300)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002300)) h
theorem e24KC2ThetaAboveLeaf0000230001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002300)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002300)) h
theorem e24KC2ThetaAboveLeaf0000230010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002300)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002300)) h
theorem e24KC2ThetaAboveLeaf0000230011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002300)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002300))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002300)) h
theorem e24KC2ThetaAboveLeaf0000230100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002301)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002301)) h
theorem e24KC2ThetaAboveLeaf0000230101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002301)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002301)) h
theorem e24KC2ThetaAboveLeaf0000230110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002301)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002301)) h
theorem e24KC2ThetaAboveLeaf0000230111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002301)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002301))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002301)) h
theorem e24KC2ThetaAboveLeaf0000230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002302)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002302)) h
theorem e24KC2ThetaAboveLeaf0000230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002302)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002302)) h
theorem e24KC2ThetaAboveLeaf0000230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002302)) = true := by
  have h : ((childHL (childLL thetaAboveCell00002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00002302)) h
theorem e24KC2ThetaAboveLeaf0000230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002302)) = true := by
  have h : ((childHH (childLL thetaAboveCell00002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00002302)) h
theorem e24KC2ThetaAboveLeaf0000230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002302)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002302)) h
theorem e24KC2ThetaAboveLeaf0000230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002302)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002302)) h
theorem e24KC2ThetaAboveLeaf0000230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002302)) = true := by
  have h : ((childHL (childLH thetaAboveCell00002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00002302)) h
theorem e24KC2ThetaAboveLeaf0000230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002302)) = true := by
  have h : ((childHH (childLH thetaAboveCell00002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00002302)) h
theorem e24KC2ThetaAboveLeaf000023022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002302) = true := by
  have h : ((childHL thetaAboveCell00002302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002302) h
theorem e24KC2ThetaAboveLeaf000023023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002302) = true := by
  have h : ((childHH thetaAboveCell00002302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002302) h
theorem e24KC2ThetaAboveLeaf0000230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002303)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002303)) h
theorem e24KC2ThetaAboveLeaf0000230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002303)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002303)) h
theorem e24KC2ThetaAboveLeaf0000230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002303)) = true := by
  have h : ((childHL (childLL thetaAboveCell00002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00002303)) h
theorem e24KC2ThetaAboveLeaf0000230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002303)) = true := by
  have h : ((childHH (childLL thetaAboveCell00002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00002303)) h
theorem e24KC2ThetaAboveLeaf0000230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002303)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002303)) h
theorem e24KC2ThetaAboveLeaf0000230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002303)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002303)) h
theorem e24KC2ThetaAboveLeaf0000230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002303)) = true := by
  have h : ((childHL (childLH thetaAboveCell00002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00002303)) h
theorem e24KC2ThetaAboveLeaf0000230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002303)) = true := by
  have h : ((childHH (childLH thetaAboveCell00002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00002303)) h
theorem e24KC2ThetaAboveLeaf000023032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002303) = true := by
  have h : ((childHL thetaAboveCell00002303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002303) h
theorem e24KC2ThetaAboveLeaf000023033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002303) = true := by
  have h : ((childHH thetaAboveCell00002303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002303) h
theorem e24KC2ThetaAboveLeaf0000231000 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002310)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002310)) h
theorem e24KC2ThetaAboveLeaf0000231001 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002310)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002310)) h
theorem e24KC2ThetaAboveLeaf0000231010 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002310)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002310)) h
theorem e24KC2ThetaAboveLeaf0000231011 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002310)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002310))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002310)) h
theorem e24KC2ThetaAboveLeaf0000231100 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002311)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002311)) h
theorem e24KC2ThetaAboveLeaf0000231101 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002311)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002311)) h
theorem e24KC2ThetaAboveLeaf0000231110 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002311)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002311)) h
theorem e24KC2ThetaAboveLeaf0000231111 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002311)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002311))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002311)) h
theorem e24KC2ThetaAboveLeaf0000231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002312)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002312)) h
theorem e24KC2ThetaAboveLeaf0000231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002312)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002312)) h
theorem e24KC2ThetaAboveLeaf0000231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002312)) = true := by
  have h : ((childHL (childLL thetaAboveCell00002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00002312)) h
theorem e24KC2ThetaAboveLeaf0000231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002312)) = true := by
  have h : ((childHH (childLL thetaAboveCell00002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00002312)) h
theorem e24KC2ThetaAboveLeaf0000231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002312)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002312)) h
theorem e24KC2ThetaAboveLeaf0000231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002312)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002312)) h
theorem e24KC2ThetaAboveLeaf0000231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002312)) = true := by
  have h : ((childHL (childLH thetaAboveCell00002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00002312)) h
theorem e24KC2ThetaAboveLeaf0000231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002312)) = true := by
  have h : ((childHH (childLH thetaAboveCell00002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00002312)) h
theorem e24KC2ThetaAboveLeaf000023122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002312) = true := by
  have h : ((childHL thetaAboveCell00002312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002312) h
theorem e24KC2ThetaAboveLeaf000023123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002312) = true := by
  have h : ((childHH thetaAboveCell00002312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002312) h
theorem e24KC2ThetaAboveLeaf0000231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell00002313)) = true := by
  have h : ((childLL (childLL thetaAboveCell00002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell00002313)) h
theorem e24KC2ThetaAboveLeaf0000231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell00002313)) = true := by
  have h : ((childLH (childLL thetaAboveCell00002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell00002313)) h
theorem e24KC2ThetaAboveLeaf0000231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002313)) = true := by
  have h : ((childHL (childLL thetaAboveCell00002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell00002313)) h
theorem e24KC2ThetaAboveLeaf0000231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002313)) = true := by
  have h : ((childHH (childLL thetaAboveCell00002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell00002313)) h
theorem e24KC2ThetaAboveLeaf0000231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell00002313)) = true := by
  have h : ((childLL (childLH thetaAboveCell00002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell00002313)) h
theorem e24KC2ThetaAboveLeaf0000231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell00002313)) = true := by
  have h : ((childLH (childLH thetaAboveCell00002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell00002313)) h
theorem e24KC2ThetaAboveLeaf0000231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002313)) = true := by
  have h : ((childHL (childLH thetaAboveCell00002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell00002313)) h
theorem e24KC2ThetaAboveLeaf0000231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002313)) = true := by
  have h : ((childHH (childLH thetaAboveCell00002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell00002313)) h
theorem e24KC2ThetaAboveLeaf000023132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00002313) = true := by
  have h : ((childHL thetaAboveCell00002313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00002313) h
theorem e24KC2ThetaAboveLeaf000023133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00002313) = true := by
  have h : ((childHH thetaAboveCell00002313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00002313) h
theorem e24KC2ThetaAboveLeaf00002320 :
    adaptiveCoverCheck 11 thetaAboveCell00002320 = true := by
  have h : (thetaAboveCell00002320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002320 h
theorem e24KC2ThetaAboveLeaf00002321 :
    adaptiveCoverCheck 11 thetaAboveCell00002321 = true := by
  have h : (thetaAboveCell00002321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002321 h
theorem e24KC2ThetaAboveLeaf00002322 :
    adaptiveCoverCheck 11 thetaAboveCell00002322 = true := by
  have h : (thetaAboveCell00002322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002322 h
theorem e24KC2ThetaAboveLeaf00002323 :
    adaptiveCoverCheck 11 thetaAboveCell00002323 = true := by
  have h : (thetaAboveCell00002323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002323 h
theorem e24KC2ThetaAboveLeaf00002330 :
    adaptiveCoverCheck 11 thetaAboveCell00002330 = true := by
  have h : (thetaAboveCell00002330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002330 h
theorem e24KC2ThetaAboveLeaf00002331 :
    adaptiveCoverCheck 11 thetaAboveCell00002331 = true := by
  have h : (thetaAboveCell00002331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002331 h
theorem e24KC2ThetaAboveLeaf00002332 :
    adaptiveCoverCheck 11 thetaAboveCell00002332 = true := by
  have h : (thetaAboveCell00002332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002332 h
theorem e24KC2ThetaAboveLeaf00002333 :
    adaptiveCoverCheck 11 thetaAboveCell00002333 = true := by
  have h : (thetaAboveCell00002333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00002333 h
theorem e24KC2ThetaAboveLeaf0000300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell0000))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell0000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell0000))) h
theorem e24KC2ThetaAboveLeaf0000301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell0000))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell0000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell0000))) h
theorem e24KC2ThetaAboveLeaf00003020 :
    adaptiveCoverCheck 11 thetaAboveCell00003020 = true := by
  have h : (thetaAboveCell00003020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003020 h
theorem e24KC2ThetaAboveLeaf00003021 :
    adaptiveCoverCheck 11 thetaAboveCell00003021 = true := by
  have h : (thetaAboveCell00003021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003021 h
theorem e24KC2ThetaAboveLeaf000030220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00003022) = true := by
  have h : ((childLL thetaAboveCell00003022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00003022) h
theorem e24KC2ThetaAboveLeaf000030221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00003022) = true := by
  have h : ((childLH thetaAboveCell00003022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00003022) h
theorem e24KC2ThetaAboveLeaf000030222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003022) = true := by
  have h : ((childHL thetaAboveCell00003022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003022) h
theorem e24KC2ThetaAboveLeaf000030223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003022) = true := by
  have h : ((childHH thetaAboveCell00003022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003022) h
theorem e24KC2ThetaAboveLeaf000030230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00003023) = true := by
  have h : ((childLL thetaAboveCell00003023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00003023) h
theorem e24KC2ThetaAboveLeaf000030231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00003023) = true := by
  have h : ((childLH thetaAboveCell00003023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00003023) h
theorem e24KC2ThetaAboveLeaf000030232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003023) = true := by
  have h : ((childHL thetaAboveCell00003023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003023) h
theorem e24KC2ThetaAboveLeaf000030233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003023) = true := by
  have h : ((childHH thetaAboveCell00003023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003023) h
theorem e24KC2ThetaAboveLeaf00003030 :
    adaptiveCoverCheck 11 thetaAboveCell00003030 = true := by
  have h : (thetaAboveCell00003030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003030 h
theorem e24KC2ThetaAboveLeaf00003031 :
    adaptiveCoverCheck 11 thetaAboveCell00003031 = true := by
  have h : (thetaAboveCell00003031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003031 h
theorem e24KC2ThetaAboveLeaf000030320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00003032) = true := by
  have h : ((childLL thetaAboveCell00003032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00003032) h
theorem e24KC2ThetaAboveLeaf000030321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00003032) = true := by
  have h : ((childLH thetaAboveCell00003032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00003032) h
theorem e24KC2ThetaAboveLeaf000030322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003032) = true := by
  have h : ((childHL thetaAboveCell00003032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003032) h
theorem e24KC2ThetaAboveLeaf000030323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003032) = true := by
  have h : ((childHH thetaAboveCell00003032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003032) h
theorem e24KC2ThetaAboveLeaf000030330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell00003033) = true := by
  have h : ((childLL thetaAboveCell00003033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell00003033) h
theorem e24KC2ThetaAboveLeaf000030331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell00003033) = true := by
  have h : ((childLH thetaAboveCell00003033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell00003033) h
theorem e24KC2ThetaAboveLeaf000030332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell00003033) = true := by
  have h : ((childHL thetaAboveCell00003033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell00003033) h
theorem e24KC2ThetaAboveLeaf000030333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell00003033) = true := by
  have h : ((childHH thetaAboveCell00003033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell00003033) h
theorem e24KC2ThetaAboveLeaf0000310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell0000))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell0000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell0000))) h
theorem e24KC2ThetaAboveLeaf0000311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell0000))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell0000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell0000))) h
theorem e24KC2ThetaAboveLeaf00003120 :
    adaptiveCoverCheck 11 thetaAboveCell00003120 = true := by
  have h : (thetaAboveCell00003120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell00003120 h

end PartE
end GerverSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchB39d17cf54d27511`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells802ef10e9d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells802ef10e9d

open CertificateCells802ef10e9d
theorem cover_subtree_f27aed8d7652 :
    adaptiveCoverCheck 7 thetaAboveCell000023102000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102000
    (by
      have h : ((childLL thetaAboveCell000023102000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102000) h)
    (by
      have h : ((childLH thetaAboveCell000023102000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102000) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102000)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102000)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102000)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102000)) h))

theorem cover_subtree_005f989c43cb :
    adaptiveCoverCheck 7 thetaAboveCell000023102001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102001
    (by
      have h : ((childLL thetaAboveCell000023102001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102001) h)
    (by
      have h : ((childLH thetaAboveCell000023102001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102001) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102001)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102001)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102001)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102001)) h))

theorem cover_subtree_9ea21eaf3506 :
    adaptiveCoverCheck 7 thetaAboveCell000023102002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102002)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102002)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102002)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102002)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102002)) h))

theorem cover_subtree_aecd625dd7fb :
    adaptiveCoverCheck 7 thetaAboveCell000023102003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102003)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102003)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102003)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102003)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102003)) h))

theorem cover_subtree_77a434675cac :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002310)))
    cover_subtree_f27aed8d7652
    cover_subtree_005f989c43cb
    cover_subtree_9ea21eaf3506
    cover_subtree_aecd625dd7fb

theorem cover_subtree_422f11b7507e :
    adaptiveCoverCheck 7 thetaAboveCell000023102010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102010
    (by
      have h : ((childLL thetaAboveCell000023102010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102010) h)
    (by
      have h : ((childLH thetaAboveCell000023102010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102010) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102010)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102010)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102010)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102010)) h))

theorem cover_subtree_9333e7948d29 :
    adaptiveCoverCheck 7 thetaAboveCell000023102011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102011
    (by
      have h : ((childLL thetaAboveCell000023102011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102011) h)
    (by
      have h : ((childLH thetaAboveCell000023102011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102011) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102011)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102011)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102011)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102011)) h))

theorem cover_subtree_0e2f446f3080 :
    adaptiveCoverCheck 7 thetaAboveCell000023102012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102012)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102012)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102012)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102012)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102012)) h))

theorem cover_subtree_07cb153dceed :
    adaptiveCoverCheck 7 thetaAboveCell000023102013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102013)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102013)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102013)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102013)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102013)) h))

theorem cover_subtree_334813029f45 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00002310)))
    cover_subtree_422f11b7507e
    cover_subtree_9333e7948d29
    cover_subtree_0e2f446f3080
    cover_subtree_07cb153dceed

theorem cover_subtree_c82ade123eba :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102020
        (by
          have h : ((childLL thetaAboveCell000023102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102020) h)
        (by
          have h : ((childLH thetaAboveCell000023102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102020) h)
        (by
          have h : ((childHL thetaAboveCell000023102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102020) h)
        (by
          have h : ((childHH thetaAboveCell000023102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102021
        (by
          have h : ((childLL thetaAboveCell000023102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102021) h)
        (by
          have h : ((childLH thetaAboveCell000023102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102021) h)
        (by
          have h : ((childHL thetaAboveCell000023102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102021) h)
        (by
          have h : ((childHH thetaAboveCell000023102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102021) h))
    (by
      have h : (thetaAboveCell000023102022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102022 h)
    (by
      have h : (thetaAboveCell000023102023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102023 h)

theorem cover_subtree_b2c2dad45076 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102030
        (by
          have h : ((childLL thetaAboveCell000023102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102030) h)
        (by
          have h : ((childLH thetaAboveCell000023102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102030) h)
        (by
          have h : ((childHL thetaAboveCell000023102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102030) h)
        (by
          have h : ((childHH thetaAboveCell000023102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102031
        (by
          have h : ((childLL thetaAboveCell000023102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102031) h)
        (by
          have h : ((childLH thetaAboveCell000023102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102031) h)
        (by
          have h : ((childHL thetaAboveCell000023102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102031) h)
        (by
          have h : ((childHH thetaAboveCell000023102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102031) h))
    (by
      have h : (thetaAboveCell000023102032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102032 h)
    (by
      have h : (thetaAboveCell000023102033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102033 h)

theorem e24KC2ThetaAboveLeaf0000231020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00002310))
    cover_subtree_77a434675cac
    cover_subtree_334813029f45
    cover_subtree_c82ade123eba
    cover_subtree_b2c2dad45076
theorem cover_subtree_d0ee7bfc8527 :
    adaptiveCoverCheck 7 thetaAboveCell000023102100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102100
    (by
      have h : ((childLL thetaAboveCell000023102100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102100) h)
    (by
      have h : ((childLH thetaAboveCell000023102100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102100) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102100)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102100)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102100)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102100)) h))

theorem cover_subtree_58a66e346033 :
    adaptiveCoverCheck 7 thetaAboveCell000023102101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102101
    (by
      have h : ((childLL thetaAboveCell000023102101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102101) h)
    (by
      have h : ((childLH thetaAboveCell000023102101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102101) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102101)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102101)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102101)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102101)) h))

theorem cover_subtree_c17867007896 :
    adaptiveCoverCheck 7 thetaAboveCell000023102102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102102)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102102)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102102)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102102)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102102)) h))

theorem cover_subtree_70f834eb3976 :
    adaptiveCoverCheck 7 thetaAboveCell000023102103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102103)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102103)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102103)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102103)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102103)) h))

theorem cover_subtree_a226aa051b7b :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00002310)))
    cover_subtree_d0ee7bfc8527
    cover_subtree_58a66e346033
    cover_subtree_c17867007896
    cover_subtree_70f834eb3976

theorem cover_subtree_71a49837eadf :
    adaptiveCoverCheck 7 thetaAboveCell000023102112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102112)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102112)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102112)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102112)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102112)) h))

theorem cover_subtree_5a86501aa891 :
    adaptiveCoverCheck 7 thetaAboveCell000023102113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023102113)
        (by
          have h : ((childLL (childLL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023102113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023102113)
        (by
          have h : ((childLL (childLH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023102113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023102113)
        (by
          have h : ((childLL (childHL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023102113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023102113)
        (by
          have h : ((childLL (childHH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023102113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023102113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023102113)) h))

theorem cover_subtree_1d4344731b0b :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102110
        (by
          have h : ((childLL thetaAboveCell000023102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102110) h)
        (by
          have h : ((childLH thetaAboveCell000023102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102110) h)
        (by
          have h : ((childHL thetaAboveCell000023102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102110) h)
        (by
          have h : ((childHH thetaAboveCell000023102110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102111
        (by
          have h : ((childLL thetaAboveCell000023102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102111) h)
        (by
          have h : ((childLH thetaAboveCell000023102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102111) h)
        (by
          have h : ((childHL thetaAboveCell000023102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102111) h)
        (by
          have h : ((childHH thetaAboveCell000023102111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102111) h))
    cover_subtree_71a49837eadf
    cover_subtree_5a86501aa891

theorem cover_subtree_3bdba90bbb0c :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102120
        (by
          have h : ((childLL thetaAboveCell000023102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102120) h)
        (by
          have h : ((childLH thetaAboveCell000023102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102120) h)
        (by
          have h : ((childHL thetaAboveCell000023102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102120) h)
        (by
          have h : ((childHH thetaAboveCell000023102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102121
        (by
          have h : ((childLL thetaAboveCell000023102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102121) h)
        (by
          have h : ((childLH thetaAboveCell000023102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102121) h)
        (by
          have h : ((childHL thetaAboveCell000023102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102121) h)
        (by
          have h : ((childHH thetaAboveCell000023102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102121) h))
    (by
      have h : (thetaAboveCell000023102122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102122 h)
    (by
      have h : (thetaAboveCell000023102123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102123 h)

theorem cover_subtree_f8da85ca8892 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102130
        (by
          have h : ((childLL thetaAboveCell000023102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102130) h)
        (by
          have h : ((childLH thetaAboveCell000023102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102130) h)
        (by
          have h : ((childHL thetaAboveCell000023102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102130) h)
        (by
          have h : ((childHH thetaAboveCell000023102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023102131
        (by
          have h : ((childLL thetaAboveCell000023102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023102131) h)
        (by
          have h : ((childLH thetaAboveCell000023102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023102131) h)
        (by
          have h : ((childHL thetaAboveCell000023102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023102131) h)
        (by
          have h : ((childHH thetaAboveCell000023102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023102131) h))
    (by
      have h : (thetaAboveCell000023102132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102132 h)
    (by
      have h : (thetaAboveCell000023102133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023102133 h)

theorem e24KC2ThetaAboveLeaf0000231021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00002310))
    cover_subtree_a226aa051b7b
    cover_subtree_1d4344731b0b
    cover_subtree_3bdba90bbb0c
    cover_subtree_f8da85ca8892
theorem e24KC2ThetaAboveLeaf0000231022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00002310))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00002310))) h)
theorem e24KC2ThetaAboveLeaf0000231023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00002310))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00002310))) h)
theorem cover_subtree_786f313d71e4 :
    adaptiveCoverCheck 7 thetaAboveCell000023103002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103002)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103002)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103002)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103002)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103002)) h))

theorem cover_subtree_7c7cbd1b1de9 :
    adaptiveCoverCheck 7 thetaAboveCell000023103003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103003)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103003)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103003)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103003)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103003)) h))

theorem cover_subtree_e95dc4fe2400 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103000
        (by
          have h : ((childLL thetaAboveCell000023103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103000) h)
        (by
          have h : ((childLH thetaAboveCell000023103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103000) h)
        (by
          have h : ((childHL thetaAboveCell000023103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103000) h)
        (by
          have h : ((childHH thetaAboveCell000023103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103001
        (by
          have h : ((childLL thetaAboveCell000023103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103001) h)
        (by
          have h : ((childLH thetaAboveCell000023103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103001) h)
        (by
          have h : ((childHL thetaAboveCell000023103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103001) h)
        (by
          have h : ((childHH thetaAboveCell000023103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103001) h))
    cover_subtree_786f313d71e4
    cover_subtree_7c7cbd1b1de9

theorem cover_subtree_d1ef0fda9310 :
    adaptiveCoverCheck 7 thetaAboveCell000023103012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103012)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103012)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103012)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103012)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103012)) h))

theorem cover_subtree_334bbbdc1a85 :
    adaptiveCoverCheck 7 thetaAboveCell000023103013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103013)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103013)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103013)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103013)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103013)) h))

theorem cover_subtree_1b4b2c805488 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103010
        (by
          have h : ((childLL thetaAboveCell000023103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103010) h)
        (by
          have h : ((childLH thetaAboveCell000023103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103010) h)
        (by
          have h : ((childHL thetaAboveCell000023103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103010) h)
        (by
          have h : ((childHH thetaAboveCell000023103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103011
        (by
          have h : ((childLL thetaAboveCell000023103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103011) h)
        (by
          have h : ((childLH thetaAboveCell000023103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103011) h)
        (by
          have h : ((childHL thetaAboveCell000023103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103011) h)
        (by
          have h : ((childHH thetaAboveCell000023103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103011) h))
    cover_subtree_d1ef0fda9310
    cover_subtree_334bbbdc1a85

theorem cover_subtree_d023ef13133b :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103020
        (by
          have h : ((childLL thetaAboveCell000023103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103020) h)
        (by
          have h : ((childLH thetaAboveCell000023103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103020) h)
        (by
          have h : ((childHL thetaAboveCell000023103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103020) h)
        (by
          have h : ((childHH thetaAboveCell000023103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103021
        (by
          have h : ((childLL thetaAboveCell000023103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103021) h)
        (by
          have h : ((childLH thetaAboveCell000023103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103021) h)
        (by
          have h : ((childHL thetaAboveCell000023103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103021) h)
        (by
          have h : ((childHH thetaAboveCell000023103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103021) h))
    (by
      have h : (thetaAboveCell000023103022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103022 h)
    (by
      have h : (thetaAboveCell000023103023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103023 h)

theorem cover_subtree_8107f33bf217 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103030
        (by
          have h : ((childLL thetaAboveCell000023103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103030) h)
        (by
          have h : ((childLH thetaAboveCell000023103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103030) h)
        (by
          have h : ((childHL thetaAboveCell000023103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103030) h)
        (by
          have h : ((childHH thetaAboveCell000023103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103031
        (by
          have h : ((childLL thetaAboveCell000023103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103031) h)
        (by
          have h : ((childLH thetaAboveCell000023103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103031) h)
        (by
          have h : ((childHL thetaAboveCell000023103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103031) h)
        (by
          have h : ((childHH thetaAboveCell000023103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103031) h))
    (by
      have h : (thetaAboveCell000023103032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103032 h)
    (by
      have h : (thetaAboveCell000023103033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103033 h)

theorem e24KC2ThetaAboveLeaf0000231030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00002310))
    cover_subtree_e95dc4fe2400
    cover_subtree_1b4b2c805488
    cover_subtree_d023ef13133b
    cover_subtree_8107f33bf217
theorem cover_subtree_e7898c3dadb7 :
    adaptiveCoverCheck 7 thetaAboveCell000023103102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103102)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103102)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103102)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103102)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103102)) h))

theorem cover_subtree_76677b2fe65f :
    adaptiveCoverCheck 7 thetaAboveCell000023103103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103103)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103103)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103103)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103103)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103103)) h))

theorem cover_subtree_b293a3c8540f :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103100
        (by
          have h : ((childLL thetaAboveCell000023103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103100) h)
        (by
          have h : ((childLH thetaAboveCell000023103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103100) h)
        (by
          have h : ((childHL thetaAboveCell000023103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103100) h)
        (by
          have h : ((childHH thetaAboveCell000023103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103101
        (by
          have h : ((childLL thetaAboveCell000023103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103101) h)
        (by
          have h : ((childLH thetaAboveCell000023103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103101) h)
        (by
          have h : ((childHL thetaAboveCell000023103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103101) h)
        (by
          have h : ((childHH thetaAboveCell000023103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103101) h))
    cover_subtree_e7898c3dadb7
    cover_subtree_76677b2fe65f

theorem cover_subtree_a17e19b0274e :
    adaptiveCoverCheck 7 thetaAboveCell000023103112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103112)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103112)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103112)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103112)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103112)) h))

theorem cover_subtree_e650c47410b7 :
    adaptiveCoverCheck 7 thetaAboveCell000023103113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023103113)
        (by
          have h : ((childLL (childLL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023103113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023103113)
        (by
          have h : ((childLL (childLH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023103113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023103113)
        (by
          have h : ((childLL (childHL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023103113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023103113)
        (by
          have h : ((childLL (childHH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023103113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023103113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023103113)) h))

theorem cover_subtree_d40c83c06c06 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103110
        (by
          have h : ((childLL thetaAboveCell000023103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103110) h)
        (by
          have h : ((childLH thetaAboveCell000023103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103110) h)
        (by
          have h : ((childHL thetaAboveCell000023103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103110) h)
        (by
          have h : ((childHH thetaAboveCell000023103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103111
        (by
          have h : ((childLL thetaAboveCell000023103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103111) h)
        (by
          have h : ((childLH thetaAboveCell000023103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103111) h)
        (by
          have h : ((childHL thetaAboveCell000023103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103111) h)
        (by
          have h : ((childHH thetaAboveCell000023103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103111) h))
    cover_subtree_a17e19b0274e
    cover_subtree_e650c47410b7

theorem cover_subtree_759d6e2f1f21 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103120
        (by
          have h : ((childLL thetaAboveCell000023103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103120) h)
        (by
          have h : ((childLH thetaAboveCell000023103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103120) h)
        (by
          have h : ((childHL thetaAboveCell000023103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103120) h)
        (by
          have h : ((childHH thetaAboveCell000023103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103121
        (by
          have h : ((childLL thetaAboveCell000023103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103121) h)
        (by
          have h : ((childLH thetaAboveCell000023103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103121) h)
        (by
          have h : ((childHL thetaAboveCell000023103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103121) h)
        (by
          have h : ((childHH thetaAboveCell000023103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103121) h))
    (by
      have h : (thetaAboveCell000023103122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103122 h)
    (by
      have h : (thetaAboveCell000023103123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103123 h)

theorem cover_subtree_695ff4e0f9a2 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00002310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00002310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103130
        (by
          have h : ((childLL thetaAboveCell000023103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103130) h)
        (by
          have h : ((childLH thetaAboveCell000023103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103130) h)
        (by
          have h : ((childHL thetaAboveCell000023103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103130) h)
        (by
          have h : ((childHH thetaAboveCell000023103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023103131
        (by
          have h : ((childLL thetaAboveCell000023103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023103131) h)
        (by
          have h : ((childLH thetaAboveCell000023103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023103131) h)
        (by
          have h : ((childHL thetaAboveCell000023103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023103131) h)
        (by
          have h : ((childHH thetaAboveCell000023103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023103131) h))
    (by
      have h : (thetaAboveCell000023103132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103132 h)
    (by
      have h : (thetaAboveCell000023103133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023103133 h)

theorem e24KC2ThetaAboveLeaf0000231031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002310))
    cover_subtree_b293a3c8540f
    cover_subtree_d40c83c06c06
    cover_subtree_759d6e2f1f21
    cover_subtree_695ff4e0f9a2
theorem e24KC2ThetaAboveLeaf0000231032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002310))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002310))) h)
theorem e24KC2ThetaAboveLeaf0000231033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002310))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002310))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002310))) h)
theorem e24KC2ThetaAboveLeaf0000231102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00002311))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00002311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023110220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110220 h)
        (by
          have h : (thetaAboveCell000023110221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110221 h)
        (by
          have h : (thetaAboveCell000023110222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110222 h)
        (by
          have h : (thetaAboveCell000023110223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023110230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110230 h)
        (by
          have h : (thetaAboveCell000023110231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110231 h)
        (by
          have h : (thetaAboveCell000023110232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110232 h)
        (by
          have h : (thetaAboveCell000023110233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110233 h))
theorem e24KC2ThetaAboveLeaf0000231103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00002311))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00002311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023110320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110320 h)
        (by
          have h : (thetaAboveCell000023110321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110321 h)
        (by
          have h : (thetaAboveCell000023110322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110322 h)
        (by
          have h : (thetaAboveCell000023110323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023110330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110330 h)
        (by
          have h : (thetaAboveCell000023110331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110331 h)
        (by
          have h : (thetaAboveCell000023110332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110332 h)
        (by
          have h : (thetaAboveCell000023110333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023110333 h))
theorem e24KC2ThetaAboveLeaf0000231112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00002311))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00002311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023111220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111220 h)
        (by
          have h : (thetaAboveCell000023111221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111221 h)
        (by
          have h : (thetaAboveCell000023111222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111222 h)
        (by
          have h : (thetaAboveCell000023111223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLH
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023111230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111230 h)
        (by
          have h : (thetaAboveCell000023111231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111231 h)
        (by
          have h : (thetaAboveCell000023111232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111232 h)
        (by
          have h : (thetaAboveCell000023111233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111233 h))
theorem e24KC2ThetaAboveLeaf0000231113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00002311))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00002311))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLH
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023111320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111320 h)
        (by
          have h : (thetaAboveCell000023111321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111321 h)
        (by
          have h : (thetaAboveCell000023111322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111322 h)
        (by
          have h : (thetaAboveCell000023111323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLH
        thetaAboveCell00002311)))
        (by
          have h : (thetaAboveCell000023111330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111330 h)
        (by
          have h : (thetaAboveCell000023111331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111331 h)
        (by
          have h : (thetaAboveCell000023111332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111332 h)
        (by
          have h : (thetaAboveCell000023111333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023111333 h))
theorem cover_subtree_b3ebd2cd2770 :
    adaptiveCoverCheck 7 thetaAboveCell000023112002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112002)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112002)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112002)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112002)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112002)) h))

theorem cover_subtree_f788d0e2a5ae :
    adaptiveCoverCheck 7 thetaAboveCell000023112003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112003)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112003)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112003)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112003)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112003)) h))

theorem cover_subtree_7f7afb8d0a4d :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112000
        (by
          have h : ((childLL thetaAboveCell000023112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112000) h)
        (by
          have h : ((childLH thetaAboveCell000023112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112000) h)
        (by
          have h : ((childHL thetaAboveCell000023112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112000) h)
        (by
          have h : ((childHH thetaAboveCell000023112000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112001
        (by
          have h : ((childLL thetaAboveCell000023112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112001) h)
        (by
          have h : ((childLH thetaAboveCell000023112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112001) h)
        (by
          have h : ((childHL thetaAboveCell000023112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112001) h)
        (by
          have h : ((childHH thetaAboveCell000023112001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112001) h))
    cover_subtree_b3ebd2cd2770
    cover_subtree_f788d0e2a5ae

theorem cover_subtree_074cd1f5f52c :
    adaptiveCoverCheck 7 thetaAboveCell000023112012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112012)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112012)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112012)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112012)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112012)) h))

theorem cover_subtree_dfbe90b65883 :
    adaptiveCoverCheck 7 thetaAboveCell000023112013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112013)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112013)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112013)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112013)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112013)) h))

theorem cover_subtree_20dd499bd364 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112010
        (by
          have h : ((childLL thetaAboveCell000023112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112010) h)
        (by
          have h : ((childLH thetaAboveCell000023112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112010) h)
        (by
          have h : ((childHL thetaAboveCell000023112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112010) h)
        (by
          have h : ((childHH thetaAboveCell000023112010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112011
        (by
          have h : ((childLL thetaAboveCell000023112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112011) h)
        (by
          have h : ((childLH thetaAboveCell000023112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112011) h)
        (by
          have h : ((childHL thetaAboveCell000023112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112011) h)
        (by
          have h : ((childHH thetaAboveCell000023112011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112011) h))
    cover_subtree_074cd1f5f52c
    cover_subtree_dfbe90b65883

theorem cover_subtree_97430f27dc25 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112020
        (by
          have h : ((childLL thetaAboveCell000023112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112020) h)
        (by
          have h : ((childLH thetaAboveCell000023112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112020) h)
        (by
          have h : ((childHL thetaAboveCell000023112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112020) h)
        (by
          have h : ((childHH thetaAboveCell000023112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112021
        (by
          have h : ((childLL thetaAboveCell000023112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112021) h)
        (by
          have h : ((childLH thetaAboveCell000023112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112021) h)
        (by
          have h : ((childHL thetaAboveCell000023112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112021) h)
        (by
          have h : ((childHH thetaAboveCell000023112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112021) h))
    (by
      have h : (thetaAboveCell000023112022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112022 h)
    (by
      have h : (thetaAboveCell000023112023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112023 h)

theorem cover_subtree_8ea35ca64562 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112030
        (by
          have h : ((childLL thetaAboveCell000023112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112030) h)
        (by
          have h : ((childLH thetaAboveCell000023112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112030) h)
        (by
          have h : ((childHL thetaAboveCell000023112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112030) h)
        (by
          have h : ((childHH thetaAboveCell000023112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112031
        (by
          have h : ((childLL thetaAboveCell000023112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112031) h)
        (by
          have h : ((childLH thetaAboveCell000023112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112031) h)
        (by
          have h : ((childHL thetaAboveCell000023112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112031) h)
        (by
          have h : ((childHH thetaAboveCell000023112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112031) h))
    (by
      have h : (thetaAboveCell000023112032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112032 h)
    (by
      have h : (thetaAboveCell000023112033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112033 h)

theorem e24KC2ThetaAboveLeaf0000231120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00002311))
    cover_subtree_7f7afb8d0a4d
    cover_subtree_20dd499bd364
    cover_subtree_97430f27dc25
    cover_subtree_8ea35ca64562
theorem cover_subtree_bb7934ab6a6d :
    adaptiveCoverCheck 7 thetaAboveCell000023112102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112102)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112102)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112102)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112102)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112102)) h))

theorem cover_subtree_f960ce5080b6 :
    adaptiveCoverCheck 7 thetaAboveCell000023112103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112103)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112103)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112103)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112103)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112103)) h))

theorem cover_subtree_be8b495598ef :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112100
        (by
          have h : ((childLL thetaAboveCell000023112100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112100) h)
        (by
          have h : ((childLH thetaAboveCell000023112100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112100) h)
        (by
          have h : ((childHL thetaAboveCell000023112100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112100) h)
        (by
          have h : ((childHH thetaAboveCell000023112100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112101
        (by
          have h : ((childLL thetaAboveCell000023112101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112101) h)
        (by
          have h : ((childLH thetaAboveCell000023112101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112101) h)
        (by
          have h : ((childHL thetaAboveCell000023112101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112101) h)
        (by
          have h : ((childHH thetaAboveCell000023112101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112101) h))
    cover_subtree_bb7934ab6a6d
    cover_subtree_f960ce5080b6

theorem cover_subtree_c24cbad7c860 :
    adaptiveCoverCheck 7 thetaAboveCell000023112112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112112)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112112)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112112)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112112)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112112)) h))

theorem cover_subtree_5030364bf316 :
    adaptiveCoverCheck 7 thetaAboveCell000023112113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023112113)
        (by
          have h : ((childLL (childLL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023112113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023112113)
        (by
          have h : ((childLL (childLH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023112113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023112113)
        (by
          have h : ((childLL (childHL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023112113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023112113)
        (by
          have h : ((childLL (childHH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023112113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023112113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023112113)) h))

theorem cover_subtree_b9cce4a71b20 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112110
        (by
          have h : ((childLL thetaAboveCell000023112110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112110) h)
        (by
          have h : ((childLH thetaAboveCell000023112110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112110) h)
        (by
          have h : ((childHL thetaAboveCell000023112110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112110) h)
        (by
          have h : ((childHH thetaAboveCell000023112110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112111
        (by
          have h : ((childLL thetaAboveCell000023112111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112111) h)
        (by
          have h : ((childLH thetaAboveCell000023112111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112111) h)
        (by
          have h : ((childHL thetaAboveCell000023112111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112111) h)
        (by
          have h : ((childHH thetaAboveCell000023112111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112111) h))
    cover_subtree_c24cbad7c860
    cover_subtree_5030364bf316

theorem cover_subtree_f376dd8d0235 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112120
        (by
          have h : ((childLL thetaAboveCell000023112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112120) h)
        (by
          have h : ((childLH thetaAboveCell000023112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112120) h)
        (by
          have h : ((childHL thetaAboveCell000023112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112120) h)
        (by
          have h : ((childHH thetaAboveCell000023112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112121
        (by
          have h : ((childLL thetaAboveCell000023112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112121) h)
        (by
          have h : ((childLH thetaAboveCell000023112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112121) h)
        (by
          have h : ((childHL thetaAboveCell000023112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112121) h)
        (by
          have h : ((childHH thetaAboveCell000023112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112121) h))
    (by
      have h : (thetaAboveCell000023112122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112122 h)
    (by
      have h : (thetaAboveCell000023112123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112123 h)

theorem cover_subtree_a9dfb54a5534 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112130
        (by
          have h : ((childLL thetaAboveCell000023112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112130) h)
        (by
          have h : ((childLH thetaAboveCell000023112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112130) h)
        (by
          have h : ((childHL thetaAboveCell000023112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112130) h)
        (by
          have h : ((childHH thetaAboveCell000023112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023112131
        (by
          have h : ((childLL thetaAboveCell000023112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023112131) h)
        (by
          have h : ((childLH thetaAboveCell000023112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023112131) h)
        (by
          have h : ((childHL thetaAboveCell000023112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023112131) h)
        (by
          have h : ((childHH thetaAboveCell000023112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023112131) h))
    (by
      have h : (thetaAboveCell000023112132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112132 h)
    (by
      have h : (thetaAboveCell000023112133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023112133 h)

theorem e24KC2ThetaAboveLeaf0000231121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00002311))
    cover_subtree_be8b495598ef
    cover_subtree_b9cce4a71b20
    cover_subtree_f376dd8d0235
    cover_subtree_a9dfb54a5534
theorem e24KC2ThetaAboveLeaf0000231122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00002311))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00002311))) h)
theorem e24KC2ThetaAboveLeaf0000231123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00002311))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00002311))) h)
theorem cover_subtree_d1cb21971feb :
    adaptiveCoverCheck 7 thetaAboveCell000023113002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113002)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113002)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113002)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023113002)
        (by
          have h : ((childLL (childHH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023113002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023113002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023113002)) h))

theorem cover_subtree_3efb79a6f9e0 :
    adaptiveCoverCheck 7 thetaAboveCell000023113003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113003)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113003)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113003)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023113003)
        (by
          have h : ((childLL (childHH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023113003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023113003)) h))

theorem cover_subtree_f6e1fff83561 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113000
        (by
          have h : ((childLL thetaAboveCell000023113000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113000) h)
        (by
          have h : ((childLH thetaAboveCell000023113000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113000) h)
        (by
          have h : ((childHL thetaAboveCell000023113000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113000) h)
        (by
          have h : ((childHH thetaAboveCell000023113000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113001
        (by
          have h : ((childLL thetaAboveCell000023113001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113001) h)
        (by
          have h : ((childLH thetaAboveCell000023113001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113001) h)
        (by
          have h : ((childHL thetaAboveCell000023113001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113001) h)
        (by
          have h : ((childHH thetaAboveCell000023113001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113001) h))
    cover_subtree_d1cb21971feb
    cover_subtree_3efb79a6f9e0

theorem cover_subtree_4cb56c792c1b :
    adaptiveCoverCheck 7 thetaAboveCell000023113012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113012)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113012)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113012)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023113012)
        (by
          have h : ((childLL (childHH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023113012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023113012)) h))

theorem cover_subtree_d84633da1a8a :
    adaptiveCoverCheck 7 thetaAboveCell000023113013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113013)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113013)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113013)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000023113013)
        (by
          have h : ((childLL (childHH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000023113013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000023113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000023113013)) h))

theorem cover_subtree_5c601c4361a5 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113010
        (by
          have h : ((childLL thetaAboveCell000023113010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113010) h)
        (by
          have h : ((childLH thetaAboveCell000023113010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113010) h)
        (by
          have h : ((childHL thetaAboveCell000023113010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113010) h)
        (by
          have h : ((childHH thetaAboveCell000023113010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113011
        (by
          have h : ((childLL thetaAboveCell000023113011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113011) h)
        (by
          have h : ((childLH thetaAboveCell000023113011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113011) h)
        (by
          have h : ((childHL thetaAboveCell000023113011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113011) h)
        (by
          have h : ((childHH thetaAboveCell000023113011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113011) h))
    cover_subtree_4cb56c792c1b
    cover_subtree_d84633da1a8a

theorem cover_subtree_7c8020e781ad :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113020
        (by
          have h : ((childLL thetaAboveCell000023113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113020) h)
        (by
          have h : ((childLH thetaAboveCell000023113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113020) h)
        (by
          have h : ((childHL thetaAboveCell000023113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113020) h)
        (by
          have h : ((childHH thetaAboveCell000023113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113021
        (by
          have h : ((childLL thetaAboveCell000023113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113021) h)
        (by
          have h : ((childLH thetaAboveCell000023113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113021) h)
        (by
          have h : ((childHL thetaAboveCell000023113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113021) h)
        (by
          have h : ((childHH thetaAboveCell000023113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113021) h))
    (by
      have h : (thetaAboveCell000023113022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113022 h)
    (by
      have h : (thetaAboveCell000023113023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113023 h)

theorem cover_subtree_01c951b510fe :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113030
        (by
          have h : ((childLL thetaAboveCell000023113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113030) h)
        (by
          have h : ((childLH thetaAboveCell000023113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113030) h)
        (by
          have h : ((childHL thetaAboveCell000023113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113030) h)
        (by
          have h : ((childHH thetaAboveCell000023113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113031
        (by
          have h : ((childLL thetaAboveCell000023113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113031) h)
        (by
          have h : ((childLH thetaAboveCell000023113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113031) h)
        (by
          have h : ((childHL thetaAboveCell000023113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113031) h)
        (by
          have h : ((childHH thetaAboveCell000023113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113031) h))
    (by
      have h : (thetaAboveCell000023113032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113032 h)
    (by
      have h : (thetaAboveCell000023113033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113033 h)

theorem e24KC2ThetaAboveLeaf0000231130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00002311))
    cover_subtree_f6e1fff83561
    cover_subtree_5c601c4361a5
    cover_subtree_7c8020e781ad
    cover_subtree_01c951b510fe
theorem cover_subtree_195c372ae99b :
    adaptiveCoverCheck 7 thetaAboveCell000023113102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113102)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113102)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000023113102)
        (by
          have h : ((childLL (childHL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000023113102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000023113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000023113102)) h))
    (by
      have h : ((childHH thetaAboveCell000023113102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113102) h)

theorem cover_subtree_d1cce1dbdb65 :
    adaptiveCoverCheck 7 thetaAboveCell000023113103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113103)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113103)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113103)) h))
    (by
      have h : ((childHL thetaAboveCell000023113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113103) h)
    (by
      have h : ((childHH thetaAboveCell000023113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113103) h)

theorem cover_subtree_f77ed6807865 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113100
        (by
          have h : ((childLL thetaAboveCell000023113100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113100) h)
        (by
          have h : ((childLH thetaAboveCell000023113100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113100) h)
        (by
          have h : ((childHL thetaAboveCell000023113100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113100) h)
        (by
          have h : ((childHH thetaAboveCell000023113100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113101
        (by
          have h : ((childLL thetaAboveCell000023113101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113101) h)
        (by
          have h : ((childLH thetaAboveCell000023113101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113101) h)
        (by
          have h : ((childHL thetaAboveCell000023113101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113101) h)
        (by
          have h : ((childHH thetaAboveCell000023113101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113101) h))
    cover_subtree_195c372ae99b
    cover_subtree_d1cce1dbdb65

theorem cover_subtree_93cb889e1841 :
    adaptiveCoverCheck 7 thetaAboveCell000023113112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113112)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113112)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113112)) h))
    (by
      have h : ((childHL thetaAboveCell000023113112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113112) h)
    (by
      have h : ((childHH thetaAboveCell000023113112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113112) h)

theorem cover_subtree_dd2e8b0050d0 :
    adaptiveCoverCheck 7 thetaAboveCell000023113113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000023113113)
        (by
          have h : ((childLL (childLL thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000023113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000023113113)
        (by
          have h : ((childLL (childLH thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000023113113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000023113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000023113113)) h))
    (by
      have h : ((childHL thetaAboveCell000023113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113113) h)
    (by
      have h : ((childHH thetaAboveCell000023113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113113) h)

theorem cover_subtree_9bd401d941dd :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113110
        (by
          have h : ((childLL thetaAboveCell000023113110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113110) h)
        (by
          have h : ((childLH thetaAboveCell000023113110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113110) h)
        (by
          have h : ((childHL thetaAboveCell000023113110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113110) h)
        (by
          have h : ((childHH thetaAboveCell000023113110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113111
        (by
          have h : ((childLL thetaAboveCell000023113111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113111) h)
        (by
          have h : ((childLH thetaAboveCell000023113111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113111) h)
        (by
          have h : ((childHL thetaAboveCell000023113111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113111) h)
        (by
          have h : ((childHH thetaAboveCell000023113111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113111) h))
    cover_subtree_93cb889e1841
    cover_subtree_dd2e8b0050d0

theorem cover_subtree_17ce5f0eb4e5 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113120
        (by
          have h : ((childLL thetaAboveCell000023113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113120) h)
        (by
          have h : ((childLH thetaAboveCell000023113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113120) h)
        (by
          have h : ((childHL thetaAboveCell000023113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113120) h)
        (by
          have h : ((childHH thetaAboveCell000023113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113121
        (by
          have h : ((childLL thetaAboveCell000023113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113121) h)
        (by
          have h : ((childLH thetaAboveCell000023113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113121) h)
        (by
          have h : ((childHL thetaAboveCell000023113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113121) h)
        (by
          have h : ((childHH thetaAboveCell000023113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113121) h))
    (by
      have h : (thetaAboveCell000023113122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113122 h)
    (by
      have h : (thetaAboveCell000023113123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113123 h)

theorem cover_subtree_167fbbc5bd30 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00002311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00002311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113130
        (by
          have h : ((childLL thetaAboveCell000023113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113130) h)
        (by
          have h : ((childLH thetaAboveCell000023113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113130) h)
        (by
          have h : ((childHL thetaAboveCell000023113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113130) h)
        (by
          have h : ((childHH thetaAboveCell000023113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000023113131
        (by
          have h : ((childLL thetaAboveCell000023113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000023113131) h)
        (by
          have h : ((childLH thetaAboveCell000023113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000023113131) h)
        (by
          have h : ((childHL thetaAboveCell000023113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000023113131) h)
        (by
          have h : ((childHH thetaAboveCell000023113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000023113131) h))
    (by
      have h : (thetaAboveCell000023113132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113132 h)
    (by
      have h : (thetaAboveCell000023113133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023113133 h)

theorem e24KC2ThetaAboveLeaf0000231131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002311))
    cover_subtree_f77ed6807865
    cover_subtree_9bd401d941dd
    cover_subtree_17ce5f0eb4e5
    cover_subtree_167fbbc5bd30
theorem e24KC2ThetaAboveLeaf0000231132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002311))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002311))) h)
theorem e24KC2ThetaAboveLeaf0000231133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002311))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002311))) h)
theorem e24KC2ThetaAboveLeaf0000320002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003200))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032000220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000220 h)
        (by
          have h : (thetaAboveCell000032000221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000221 h)
        (by
          have h : (thetaAboveCell000032000222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000222 h)
        (by
          have h : (thetaAboveCell000032000223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032000230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000230 h)
        (by
          have h : (thetaAboveCell000032000231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000231 h)
        (by
          have h : (thetaAboveCell000032000232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000232 h)
        (by
          have h : (thetaAboveCell000032000233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000233 h))
theorem e24KC2ThetaAboveLeaf0000320003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003200))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032000320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000320 h)
        (by
          have h : (thetaAboveCell000032000321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000321 h)
        (by
          have h : (thetaAboveCell000032000322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000322 h)
        (by
          have h : (thetaAboveCell000032000323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032000330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000330 h)
        (by
          have h : (thetaAboveCell000032000331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000331 h)
        (by
          have h : (thetaAboveCell000032000332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000332 h)
        (by
          have h : (thetaAboveCell000032000333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032000333 h))
theorem e24KC2ThetaAboveLeaf0000320012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003200))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003200))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00003200)))
        (by
          have h : (thetaAboveCell000032001220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032001220 h)
        (by
          have h : (thetaAboveCell000032001221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032001221 h)
        (by
          have h : (thetaAboveCell000032001222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032001222 h)
        (by
          have h : (thetaAboveCell000032001223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032001223 h))
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003200))) h)
theorem e24KC2ThetaAboveLeaf0000320013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003200))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003200))) h)
theorem cover_subtree_dc923db2d444 :
    adaptiveCoverCheck 7 thetaAboveCell000032002002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000032002002)
        (by
          have h : ((childLL (childLL thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000032002002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000032002002)
        (by
          have h : ((childLL (childLH thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000032002002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000032002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000032002002)) h))
    (by
      have h : ((childHL thetaAboveCell000032002002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002002) h)
    (by
      have h : ((childHH thetaAboveCell000032002002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002002) h)

theorem cover_subtree_3d16a69d20d7 :
    adaptiveCoverCheck 7 thetaAboveCell000032002003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000032002003)
        (by
          have h : ((childLL (childLL thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000032002003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000032002003)
        (by
          have h : ((childLL (childLH thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000032002003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000032002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000032002003)) h))
    (by
      have h : ((childHL thetaAboveCell000032002003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002003) h)
    (by
      have h : ((childHH thetaAboveCell000032002003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002003) h)

theorem cover_subtree_80a354cc93c8 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002000
        (by
          have h : ((childLL thetaAboveCell000032002000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002000) h)
        (by
          have h : ((childLH thetaAboveCell000032002000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002000) h)
        (by
          have h : ((childHL thetaAboveCell000032002000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002000) h)
        (by
          have h : ((childHH thetaAboveCell000032002000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002001
        (by
          have h : ((childLL thetaAboveCell000032002001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002001) h)
        (by
          have h : ((childLH thetaAboveCell000032002001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002001) h)
        (by
          have h : ((childHL thetaAboveCell000032002001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002001) h)
        (by
          have h : ((childHH thetaAboveCell000032002001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002001) h))
    cover_subtree_dc923db2d444
    cover_subtree_3d16a69d20d7

theorem cover_subtree_0a679df94e2d :
    adaptiveCoverCheck 7 thetaAboveCell000032002012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000032002012)
        (by
          have h : ((childLL (childLL thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000032002012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000032002012)
        (by
          have h : ((childLL (childLH thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000032002012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000032002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000032002012)) h))
    (by
      have h : ((childHL thetaAboveCell000032002012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002012) h)
    (by
      have h : ((childHH thetaAboveCell000032002012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002012) h)

theorem cover_subtree_a9518d4839ee :
    adaptiveCoverCheck 7 thetaAboveCell000032002013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000032002013)
        (by
          have h : ((childLL (childLL thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000032002013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000032002013)
        (by
          have h : ((childLL (childLH thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000032002013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000032002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000032002013)) h))
    (by
      have h : ((childHL thetaAboveCell000032002013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002013) h)
    (by
      have h : ((childHH thetaAboveCell000032002013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002013) h)

theorem cover_subtree_69eb32740a9f :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002010
        (by
          have h : ((childLL thetaAboveCell000032002010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002010) h)
        (by
          have h : ((childLH thetaAboveCell000032002010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002010) h)
        (by
          have h : ((childHL thetaAboveCell000032002010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002010) h)
        (by
          have h : ((childHH thetaAboveCell000032002010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002011
        (by
          have h : ((childLL thetaAboveCell000032002011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002011) h)
        (by
          have h : ((childLH thetaAboveCell000032002011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002011) h)
        (by
          have h : ((childHL thetaAboveCell000032002011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002011) h)
        (by
          have h : ((childHH thetaAboveCell000032002011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002011) h))
    cover_subtree_0a679df94e2d
    cover_subtree_a9518d4839ee

theorem cover_subtree_0afe6e641e2b :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002020
        (by
          have h : ((childLL thetaAboveCell000032002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002020) h)
        (by
          have h : ((childLH thetaAboveCell000032002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002020) h)
        (by
          have h : ((childHL thetaAboveCell000032002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002020) h)
        (by
          have h : ((childHH thetaAboveCell000032002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002021
        (by
          have h : ((childLL thetaAboveCell000032002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002021) h)
        (by
          have h : ((childLH thetaAboveCell000032002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002021) h)
        (by
          have h : ((childHL thetaAboveCell000032002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002021) h)
        (by
          have h : ((childHH thetaAboveCell000032002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002021) h))
    (by
      have h : (thetaAboveCell000032002022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002022 h)
    (by
      have h : (thetaAboveCell000032002023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002023 h)

theorem cover_subtree_13f8c37ba985 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002030
        (by
          have h : ((childLL thetaAboveCell000032002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002030) h)
        (by
          have h : ((childLH thetaAboveCell000032002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002030) h)
        (by
          have h : ((childHL thetaAboveCell000032002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002030) h)
        (by
          have h : ((childHH thetaAboveCell000032002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002031
        (by
          have h : ((childLL thetaAboveCell000032002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002031) h)
        (by
          have h : ((childLH thetaAboveCell000032002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002031) h)
        (by
          have h : ((childHL thetaAboveCell000032002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002031) h)
        (by
          have h : ((childHH thetaAboveCell000032002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002031) h))
    (by
      have h : (thetaAboveCell000032002032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002032 h)
    (by
      have h : (thetaAboveCell000032002033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002033 h)

theorem e24KC2ThetaAboveLeaf0000320020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003200))
    cover_subtree_80a354cc93c8
    cover_subtree_69eb32740a9f
    cover_subtree_0afe6e641e2b
    cover_subtree_13f8c37ba985
theorem cover_subtree_6185ee76a9ce :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002100
        (by
          have h : ((childLL thetaAboveCell000032002100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002100) h)
        (by
          have h : ((childLH thetaAboveCell000032002100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002100) h)
        (by
          have h : ((childHL thetaAboveCell000032002100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002100) h)
        (by
          have h : ((childHH thetaAboveCell000032002100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002101
        (by
          have h : ((childLL thetaAboveCell000032002101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002101) h)
        (by
          have h : ((childLH thetaAboveCell000032002101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002101) h)
        (by
          have h : ((childHL thetaAboveCell000032002101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002101) h)
        (by
          have h : ((childHH thetaAboveCell000032002101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002101) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002102
        (by
          have h : ((childLL thetaAboveCell000032002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002102) h)
        (by
          have h : ((childLH thetaAboveCell000032002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002102) h)
        (by
          have h : ((childHL thetaAboveCell000032002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002102) h)
        (by
          have h : ((childHH thetaAboveCell000032002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002103
        (by
          have h : ((childLL thetaAboveCell000032002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002103) h)
        (by
          have h : ((childLH thetaAboveCell000032002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002103) h)
        (by
          have h : ((childHL thetaAboveCell000032002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002103) h)
        (by
          have h : ((childHH thetaAboveCell000032002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002103) h))

theorem cover_subtree_d6e21884e5c8 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002110
        (by
          have h : ((childLL thetaAboveCell000032002110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002110) h)
        (by
          have h : ((childLH thetaAboveCell000032002110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002110) h)
        (by
          have h : ((childHL thetaAboveCell000032002110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002110) h)
        (by
          have h : ((childHH thetaAboveCell000032002110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002111
        (by
          have h : ((childLL thetaAboveCell000032002111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002111) h)
        (by
          have h : ((childLH thetaAboveCell000032002111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002111) h)
        (by
          have h : ((childHL thetaAboveCell000032002111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002111) h)
        (by
          have h : ((childHH thetaAboveCell000032002111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002111) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002112
        (by
          have h : ((childLL thetaAboveCell000032002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002112) h)
        (by
          have h : ((childLH thetaAboveCell000032002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002112) h)
        (by
          have h : ((childHL thetaAboveCell000032002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002112) h)
        (by
          have h : ((childHH thetaAboveCell000032002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002113
        (by
          have h : ((childLL thetaAboveCell000032002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002113) h)
        (by
          have h : ((childLH thetaAboveCell000032002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002113) h)
        (by
          have h : ((childHL thetaAboveCell000032002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002113) h)
        (by
          have h : ((childHH thetaAboveCell000032002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002113) h))

theorem cover_subtree_d4ae0081215d :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002120
        (by
          have h : ((childLL thetaAboveCell000032002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002120) h)
        (by
          have h : ((childLH thetaAboveCell000032002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002120) h)
        (by
          have h : ((childHL thetaAboveCell000032002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002120) h)
        (by
          have h : ((childHH thetaAboveCell000032002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002121
        (by
          have h : ((childLL thetaAboveCell000032002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002121) h)
        (by
          have h : ((childLH thetaAboveCell000032002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002121) h)
        (by
          have h : ((childHL thetaAboveCell000032002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002121) h)
        (by
          have h : ((childHH thetaAboveCell000032002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002121) h))
    (by
      have h : (thetaAboveCell000032002122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002122 h)
    (by
      have h : (thetaAboveCell000032002123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002123 h)

theorem cover_subtree_14b21c11f4bb :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002130
        (by
          have h : ((childLL thetaAboveCell000032002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002130) h)
        (by
          have h : ((childLH thetaAboveCell000032002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002130) h)
        (by
          have h : ((childHL thetaAboveCell000032002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002130) h)
        (by
          have h : ((childHH thetaAboveCell000032002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032002131
        (by
          have h : ((childLL thetaAboveCell000032002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032002131) h)
        (by
          have h : ((childLH thetaAboveCell000032002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032002131) h)
        (by
          have h : ((childHL thetaAboveCell000032002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032002131) h)
        (by
          have h : ((childHH thetaAboveCell000032002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032002131) h))
    (by
      have h : (thetaAboveCell000032002132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002132 h)
    (by
      have h : (thetaAboveCell000032002133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032002133 h)

theorem e24KC2ThetaAboveLeaf0000320021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003200))
    cover_subtree_6185ee76a9ce
    cover_subtree_d6e21884e5c8
    cover_subtree_d4ae0081215d
    cover_subtree_14b21c11f4bb
theorem e24KC2ThetaAboveLeaf0000320022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003200))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003200))) h)
theorem e24KC2ThetaAboveLeaf0000320023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003200))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003200))) h)
theorem cover_subtree_0c3f9f5d2a22 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003000
        (by
          have h : ((childLL thetaAboveCell000032003000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003000) h)
        (by
          have h : ((childLH thetaAboveCell000032003000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003000) h)
        (by
          have h : ((childHL thetaAboveCell000032003000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003000) h)
        (by
          have h : ((childHH thetaAboveCell000032003000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003001
        (by
          have h : ((childLL thetaAboveCell000032003001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003001) h)
        (by
          have h : ((childLH thetaAboveCell000032003001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003001) h)
        (by
          have h : ((childHL thetaAboveCell000032003001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003001) h)
        (by
          have h : ((childHH thetaAboveCell000032003001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003001) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003002
        (by
          have h : ((childLL thetaAboveCell000032003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003002) h)
        (by
          have h : ((childLH thetaAboveCell000032003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003002) h)
        (by
          have h : ((childHL thetaAboveCell000032003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003002) h)
        (by
          have h : ((childHH thetaAboveCell000032003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003003
        (by
          have h : ((childLL thetaAboveCell000032003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003003) h)
        (by
          have h : ((childLH thetaAboveCell000032003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003003) h)
        (by
          have h : ((childHL thetaAboveCell000032003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003003) h)
        (by
          have h : ((childHH thetaAboveCell000032003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003003) h))

theorem cover_subtree_e68bbaf0142c :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003010
        (by
          have h : ((childLL thetaAboveCell000032003010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003010) h)
        (by
          have h : ((childLH thetaAboveCell000032003010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003010) h)
        (by
          have h : ((childHL thetaAboveCell000032003010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003010) h)
        (by
          have h : ((childHH thetaAboveCell000032003010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003011
        (by
          have h : ((childLL thetaAboveCell000032003011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003011) h)
        (by
          have h : ((childLH thetaAboveCell000032003011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003011) h)
        (by
          have h : ((childHL thetaAboveCell000032003011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003011) h)
        (by
          have h : ((childHH thetaAboveCell000032003011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003011) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003012
        (by
          have h : ((childLL thetaAboveCell000032003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003012) h)
        (by
          have h : ((childLH thetaAboveCell000032003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003012) h)
        (by
          have h : ((childHL thetaAboveCell000032003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003012) h)
        (by
          have h : ((childHH thetaAboveCell000032003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003013
        (by
          have h : ((childLL thetaAboveCell000032003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003013) h)
        (by
          have h : ((childLH thetaAboveCell000032003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003013) h)
        (by
          have h : ((childHL thetaAboveCell000032003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003013) h)
        (by
          have h : ((childHH thetaAboveCell000032003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003013) h))

theorem cover_subtree_80b59cc08427 :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003020
        (by
          have h : ((childLL thetaAboveCell000032003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003020) h)
        (by
          have h : ((childLH thetaAboveCell000032003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003020) h)
        (by
          have h : ((childHL thetaAboveCell000032003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003020) h)
        (by
          have h : ((childHH thetaAboveCell000032003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003021
        (by
          have h : ((childLL thetaAboveCell000032003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003021) h)
        (by
          have h : ((childLH thetaAboveCell000032003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003021) h)
        (by
          have h : ((childHL thetaAboveCell000032003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003021) h)
        (by
          have h : ((childHH thetaAboveCell000032003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003021) h))
    (by
      have h : (thetaAboveCell000032003022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003022 h)
    (by
      have h : (thetaAboveCell000032003023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003023 h)

theorem cover_subtree_45a4c3e7665d :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003030
        (by
          have h : ((childLL thetaAboveCell000032003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003030) h)
        (by
          have h : ((childLH thetaAboveCell000032003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003030) h)
        (by
          have h : ((childHL thetaAboveCell000032003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003030) h)
        (by
          have h : ((childHH thetaAboveCell000032003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003031
        (by
          have h : ((childLL thetaAboveCell000032003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003031) h)
        (by
          have h : ((childLH thetaAboveCell000032003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003031) h)
        (by
          have h : ((childHL thetaAboveCell000032003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003031) h)
        (by
          have h : ((childHH thetaAboveCell000032003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003031) h))
    (by
      have h : (thetaAboveCell000032003032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003032 h)
    (by
      have h : (thetaAboveCell000032003033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003033 h)

theorem e24KC2ThetaAboveLeaf0000320030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003200))
    cover_subtree_0c3f9f5d2a22
    cover_subtree_e68bbaf0142c
    cover_subtree_80b59cc08427
    cover_subtree_45a4c3e7665d
theorem cover_subtree_cabec6ebeaec :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003100
        (by
          have h : ((childLL thetaAboveCell000032003100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003100) h)
        (by
          have h : ((childLH thetaAboveCell000032003100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003100) h)
        (by
          have h : ((childHL thetaAboveCell000032003100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003100) h)
        (by
          have h : ((childHH thetaAboveCell000032003100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003101
        (by
          have h : ((childLL thetaAboveCell000032003101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003101) h)
        (by
          have h : ((childLH thetaAboveCell000032003101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003101) h)
        (by
          have h : ((childHL thetaAboveCell000032003101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003101) h)
        (by
          have h : ((childHH thetaAboveCell000032003101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003101) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003102
        (by
          have h : ((childLL thetaAboveCell000032003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003102) h)
        (by
          have h : ((childLH thetaAboveCell000032003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003102) h)
        (by
          have h : ((childHL thetaAboveCell000032003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003102) h)
        (by
          have h : ((childHH thetaAboveCell000032003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003103
        (by
          have h : ((childLL thetaAboveCell000032003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003103) h)
        (by
          have h : ((childLH thetaAboveCell000032003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003103) h)
        (by
          have h : ((childHL thetaAboveCell000032003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003103) h)
        (by
          have h : ((childHH thetaAboveCell000032003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003103) h))

theorem cover_subtree_f94fc5a27c16 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003110
        (by
          have h : ((childLL thetaAboveCell000032003110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003110) h)
        (by
          have h : ((childLH thetaAboveCell000032003110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003110) h)
        (by
          have h : ((childHL thetaAboveCell000032003110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003110) h)
        (by
          have h : ((childHH thetaAboveCell000032003110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003111
        (by
          have h : ((childLL thetaAboveCell000032003111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003111) h)
        (by
          have h : ((childLH thetaAboveCell000032003111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003111) h)
        (by
          have h : ((childHL thetaAboveCell000032003111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003111) h)
        (by
          have h : ((childHH thetaAboveCell000032003111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003111) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003112
        (by
          have h : ((childLL thetaAboveCell000032003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003112) h)
        (by
          have h : ((childLH thetaAboveCell000032003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003112) h)
        (by
          have h : ((childHL thetaAboveCell000032003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003112) h)
        (by
          have h : ((childHH thetaAboveCell000032003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003113
        (by
          have h : ((childLL thetaAboveCell000032003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003113) h)
        (by
          have h : ((childLH thetaAboveCell000032003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003113) h)
        (by
          have h : ((childHL thetaAboveCell000032003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003113) h)
        (by
          have h : ((childHH thetaAboveCell000032003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003113) h))

theorem cover_subtree_5a58662c5bc0 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003120
        (by
          have h : ((childLL thetaAboveCell000032003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003120) h)
        (by
          have h : ((childLH thetaAboveCell000032003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003120) h)
        (by
          have h : ((childHL thetaAboveCell000032003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003120) h)
        (by
          have h : ((childHH thetaAboveCell000032003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003121
        (by
          have h : ((childLL thetaAboveCell000032003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003121) h)
        (by
          have h : ((childLH thetaAboveCell000032003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003121) h)
        (by
          have h : ((childHL thetaAboveCell000032003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003121) h)
        (by
          have h : ((childHH thetaAboveCell000032003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003121) h))
    (by
      have h : (thetaAboveCell000032003122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003122 h)
    (by
      have h : (thetaAboveCell000032003123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003123 h)

theorem cover_subtree_38aaf5d7c82e :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003130
        (by
          have h : ((childLL thetaAboveCell000032003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003130) h)
        (by
          have h : ((childLH thetaAboveCell000032003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003130) h)
        (by
          have h : ((childHL thetaAboveCell000032003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003130) h)
        (by
          have h : ((childHH thetaAboveCell000032003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032003131
        (by
          have h : ((childLL thetaAboveCell000032003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032003131) h)
        (by
          have h : ((childLH thetaAboveCell000032003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032003131) h)
        (by
          have h : ((childHL thetaAboveCell000032003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032003131) h)
        (by
          have h : ((childHH thetaAboveCell000032003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032003131) h))
    (by
      have h : (thetaAboveCell000032003132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003132 h)
    (by
      have h : (thetaAboveCell000032003133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032003133 h)

theorem e24KC2ThetaAboveLeaf0000320031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003200))
    cover_subtree_cabec6ebeaec
    cover_subtree_f94fc5a27c16
    cover_subtree_5a58662c5bc0
    cover_subtree_38aaf5d7c82e
theorem e24KC2ThetaAboveLeaf0000320032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003200))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003200))) h)
theorem e24KC2ThetaAboveLeaf0000320033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003200))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003200))) h)
theorem e24KC2ThetaAboveLeaf0000320102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003201))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003201))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003201))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003201))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003201))) h)

end PartE
end GerverSofa

end

end

end

end

end

end
