/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch017`.
* `GerverSofa.KernelOnly.PartE.Certificates.Batch021`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells2af6f575e7

/-- Subcell `1110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1112 : AngleCell :=
  childHL (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1113 : AngleCell :=
  childHH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1120 : AngleCell :=
  childLL (childHL (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1121 : AngleCell :=
  childLH (childHL (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1122 : AngleCell :=
  childHL (childHL (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1123 : AngleCell :=
  childHH (childHL (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1130 : AngleCell :=
  childLL (childHH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1131 : AngleCell :=
  childLH (childHH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1132 : AngleCell :=
  childHL (childHH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1133 : AngleCell :=
  childHH (childHH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `1300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1300 : AngleCell :=
  childLL (childLL (childHH (childLH e24ThetaBelowRoot)))

/-- Subcell `1301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1301 : AngleCell :=
  childLH (childLL (childHH (childLH e24ThetaBelowRoot)))

/-- Subcell `1302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1302 : AngleCell :=
  childHL (childLL (childHH (childLH e24ThetaBelowRoot)))

/-- Subcell `1303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1303 : AngleCell :=
  childHH (childLL (childHH (childLH e24ThetaBelowRoot)))

/-- Subcell `1310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1310 : AngleCell :=
  childLL (childLH (childHH (childLH e24ThetaBelowRoot)))

/-- Subcell `1311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1311 : AngleCell :=
  childLH (childLH (childHH (childLH e24ThetaBelowRoot)))

/-- Subcell `1312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1312 : AngleCell :=
  childHL (childLH (childHH (childLH e24ThetaBelowRoot)))

/-- Subcell `1313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1313 : AngleCell :=
  childHH (childLH (childHH (childLH e24ThetaBelowRoot)))

/-- Subcell `11103020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1110)))

/-- Subcell `11103100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1110)))

/-- Subcell `11103200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaBelowCell1110)))

/-- Subcell `11103300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11103313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaBelowCell1110)))

/-- Subcell `11112000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell1111)))

/-- Subcell `11112100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1111)))

/-- Subcell `11112200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaBelowCell1111)))

/-- Subcell `11112302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11112333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaBelowCell1111)))

/-- Subcell `11113020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1111)))

/-- Subcell `11113120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1111)))

/-- Subcell `11113202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaBelowCell1111)))

/-- Subcell `11113302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `11113333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCells2af6f575e7

namespace GerverSofa.PartE.CertificateCellsc9f578345f

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002200)))

/-- Subcell `000022010220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00002201)))

/-- Subcell `000022010221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00002201)))

/-- Subcell `000022010222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00002201)))

/-- Subcell `000022010223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00002201)))

/-- Subcell `000022010230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00002201)))

/-- Subcell `000022010231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00002201)))

/-- Subcell `000022010232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00002201)))

/-- Subcell `000022010233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00002201)))

/-- Subcell `000022010320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00002201)))

/-- Subcell `000022010321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00002201)))

/-- Subcell `000022010322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00002201)))

/-- Subcell `000022010323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00002201)))

/-- Subcell `000022010330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00002201)))

/-- Subcell `000022010331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00002201)))

/-- Subcell `000022010332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00002201)))

/-- Subcell `000022010333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022010333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00002201)))

/-- Subcell `000022011220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00002201)))

/-- Subcell `000022011221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00002201)))

/-- Subcell `000022011222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00002201)))

/-- Subcell `000022011223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00002201)))

/-- Subcell `000022011230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaAboveCell00002201)))

/-- Subcell `000022011231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaAboveCell00002201)))

/-- Subcell `000022011232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaAboveCell00002201)))

/-- Subcell `000022011233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaAboveCell00002201)))

/-- Subcell `000022011320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaAboveCell00002201)))

/-- Subcell `000022011321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaAboveCell00002201)))

/-- Subcell `000022011322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaAboveCell00002201)))

/-- Subcell `000022011323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaAboveCell00002201)))

/-- Subcell `000022011330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaAboveCell00002201)))

/-- Subcell `000022011331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaAboveCell00002201)))

/-- Subcell `000022011332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaAboveCell00002201)))

/-- Subcell `000022011333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022011333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaAboveCell00002201)))

/-- Subcell `000022012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `000022012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00002201)))

/-- Subcell `0000220031002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022003100)))

/-- Subcell `0000220031003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022003100)))

/-- Subcell `0000220031012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022003101)))

/-- Subcell `0000220031013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022003101)))

/-- Subcell `0000220031102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022003110)))

/-- Subcell `0000220031103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022003110)))

/-- Subcell `0000220031112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022003111)))

/-- Subcell `0000220031113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220031113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220031113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022003111)))

/-- Subcell `0000220120002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022012000)))

/-- Subcell `0000220120003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022012000)))

/-- Subcell `0000220120012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022012001)))

/-- Subcell `0000220120013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022012001)))

/-- Subcell `0000220120102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022012010)))

/-- Subcell `0000220120103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022012010)))

/-- Subcell `0000220120112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022012011)))

/-- Subcell `0000220120113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell000022012011)))

/-- Subcell `0000220120113333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220120113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell000022012011)))

end GerverSofa.PartE.CertificateCellsc9f578345f

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT716800017`.
-/

public section

noncomputable section

section

/-! E24KC5 checkpoint-aware kernel batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2af6f575e7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2af6f575e7

open CertificateCells2af6f575e7
theorem e24KC2ThetaBelowLeaf111030203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103020) = true := by
  have h : ((childHH thetaBelowCell11103020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103020) h
theorem e24KC2ThetaBelowLeaf111030210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103021) = true := by
  have h : ((childLL thetaBelowCell11103021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103021) h
theorem e24KC2ThetaBelowLeaf111030211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103021) = true := by
  have h : ((childLH thetaBelowCell11103021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103021) h
theorem e24KC2ThetaBelowLeaf111030212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103021) = true := by
  have h : ((childHL thetaBelowCell11103021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103021) h
theorem e24KC2ThetaBelowLeaf111030213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103021) = true := by
  have h : ((childHH thetaBelowCell11103021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103021) h
theorem e24KC2ThetaBelowLeaf111030220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103022) = true := by
  have h : ((childLL thetaBelowCell11103022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103022) h
theorem e24KC2ThetaBelowLeaf111030221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103022) = true := by
  have h : ((childLH thetaBelowCell11103022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103022) h
theorem e24KC2ThetaBelowLeaf111030222 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103022) = true := by
  have h : ((childHL thetaBelowCell11103022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103022) h
theorem e24KC2ThetaBelowLeaf111030230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103023) = true := by
  have h : ((childLL thetaBelowCell11103023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103023) h
theorem e24KC2ThetaBelowLeaf111030231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103023) = true := by
  have h : ((childLH thetaBelowCell11103023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103023) h
theorem e24KC2ThetaBelowLeaf111030300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103030) = true := by
  have h : ((childLL thetaBelowCell11103030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103030) h
theorem e24KC2ThetaBelowLeaf111030301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103030) = true := by
  have h : ((childLH thetaBelowCell11103030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103030) h
theorem e24KC2ThetaBelowLeaf111030302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103030) = true := by
  have h : ((childHL thetaBelowCell11103030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103030) h
theorem e24KC2ThetaBelowLeaf111030303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103030) = true := by
  have h : ((childHH thetaBelowCell11103030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103030) h
theorem e24KC2ThetaBelowLeaf111030310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103031) = true := by
  have h : ((childLL thetaBelowCell11103031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103031) h
theorem e24KC2ThetaBelowLeaf111030311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103031) = true := by
  have h : ((childLH thetaBelowCell11103031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103031) h
theorem e24KC2ThetaBelowLeaf11103100 :
    adaptiveCoverCheck 10 thetaBelowCell11103100 = true := by
  have h : (thetaBelowCell11103100).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103100 h
theorem e24KC2ThetaBelowLeaf11103101 :
    adaptiveCoverCheck 10 thetaBelowCell11103101 = true := by
  have h : (thetaBelowCell11103101).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103101 h
theorem e24KC2ThetaBelowLeaf11103102 :
    adaptiveCoverCheck 10 thetaBelowCell11103102 = true := by
  have h : (thetaBelowCell11103102).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103102 h
theorem e24KC2ThetaBelowLeaf11103103 :
    adaptiveCoverCheck 10 thetaBelowCell11103103 = true := by
  have h : (thetaBelowCell11103103).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103103 h
theorem e24KC2ThetaBelowLeaf11103110 :
    adaptiveCoverCheck 10 thetaBelowCell11103110 = true := by
  have h : (thetaBelowCell11103110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103110 h
theorem e24KC2ThetaBelowLeaf11103111 :
    adaptiveCoverCheck 10 thetaBelowCell11103111 = true := by
  have h : (thetaBelowCell11103111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103111 h
theorem e24KC2ThetaBelowLeaf11103112 :
    adaptiveCoverCheck 10 thetaBelowCell11103112 = true := by
  have h : (thetaBelowCell11103112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103112 h
theorem e24KC2ThetaBelowLeaf11103113 :
    adaptiveCoverCheck 10 thetaBelowCell11103113 = true := by
  have h : (thetaBelowCell11103113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103113 h
theorem e24KC2ThetaBelowLeaf111031200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103120) = true := by
  have h : ((childLL thetaBelowCell11103120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103120) h
theorem e24KC2ThetaBelowLeaf111031201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103120) = true := by
  have h : ((childLH thetaBelowCell11103120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103120) h
theorem e24KC2ThetaBelowLeaf111031203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103120) = true := by
  have h : ((childHH thetaBelowCell11103120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103120) h
theorem e24KC2ThetaBelowLeaf111031210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103121) = true := by
  have h : ((childLL thetaBelowCell11103121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103121) h
theorem e24KC2ThetaBelowLeaf111031211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103121) = true := by
  have h : ((childLH thetaBelowCell11103121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103121) h
theorem e24KC2ThetaBelowLeaf111031212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103121) = true := by
  have h : ((childHL thetaBelowCell11103121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103121) h
theorem e24KC2ThetaBelowLeaf111031213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103121) = true := by
  have h : ((childHH thetaBelowCell11103121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103121) h
theorem e24KC2ThetaBelowLeaf111031300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103130) = true := by
  have h : ((childLL thetaBelowCell11103130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103130) h
theorem e24KC2ThetaBelowLeaf111031301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103130) = true := by
  have h : ((childLH thetaBelowCell11103130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103130) h
theorem e24KC2ThetaBelowLeaf111031302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103130) = true := by
  have h : ((childHL thetaBelowCell11103130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103130) h
theorem e24KC2ThetaBelowLeaf111031303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103130) = true := by
  have h : ((childHH thetaBelowCell11103130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103130) h
theorem e24KC2ThetaBelowLeaf111031310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103131) = true := by
  have h : ((childLL thetaBelowCell11103131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103131) h
theorem e24KC2ThetaBelowLeaf111031311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103131) = true := by
  have h : ((childLH thetaBelowCell11103131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103131) h
theorem e24KC2ThetaBelowLeaf111031312 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103131) = true := by
  have h : ((childHL thetaBelowCell11103131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103131) h
theorem e24KC2ThetaBelowLeaf111031313 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103131) = true := by
  have h : ((childHH thetaBelowCell11103131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103131) h
theorem e24KC2ThetaBelowLeaf111032000 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103200) = true := by
  have h : ((childLL thetaBelowCell11103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103200) h
theorem e24KC2ThetaBelowLeaf111032001 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103200) = true := by
  have h : ((childLH thetaBelowCell11103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103200) h
theorem e24KC2ThetaBelowLeaf111032002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103200) = true := by
  have h : ((childHL thetaBelowCell11103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103200) h
theorem e24KC2ThetaBelowLeaf111032003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103200) = true := by
  have h : ((childHH thetaBelowCell11103200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103200) h
theorem e24KC2ThetaBelowLeaf111032010 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11103201) = true := by
  have h : ((childLL thetaBelowCell11103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11103201) h
theorem e24KC2ThetaBelowLeaf111032011 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11103201) = true := by
  have h : ((childLH thetaBelowCell11103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11103201) h
theorem e24KC2ThetaBelowLeaf111032012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103201) = true := by
  have h : ((childHL thetaBelowCell11103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103201) h
theorem e24KC2ThetaBelowLeaf111032013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103201) = true := by
  have h : ((childHH thetaBelowCell11103201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103201) h
theorem e24KC2ThetaBelowLeaf11103202 :
    adaptiveCoverCheck 10 thetaBelowCell11103202 = true := by
  have h : (thetaBelowCell11103202).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103202 h
theorem e24KC2ThetaBelowLeaf11103203 :
    adaptiveCoverCheck 10 thetaBelowCell11103203 = true := by
  have h : (thetaBelowCell11103203).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103203 h
theorem e24KC2ThetaBelowLeaf111032102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103210) = true := by
  have h : ((childHL thetaBelowCell11103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103210) h
theorem e24KC2ThetaBelowLeaf111032103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103210) = true := by
  have h : ((childHH thetaBelowCell11103210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103210) h
theorem e24KC2ThetaBelowLeaf111032112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103211) = true := by
  have h : ((childHL thetaBelowCell11103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103211) h
theorem e24KC2ThetaBelowLeaf111032113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103211) = true := by
  have h : ((childHH thetaBelowCell11103211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103211) h
theorem e24KC2ThetaBelowLeaf11103212 :
    adaptiveCoverCheck 10 thetaBelowCell11103212 = true := by
  have h : (thetaBelowCell11103212).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103212 h
theorem e24KC2ThetaBelowLeaf11103213 :
    adaptiveCoverCheck 10 thetaBelowCell11103213 = true := by
  have h : (thetaBelowCell11103213).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103213 h
theorem e24KC2ThetaBelowLeaf1110322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1110))) = true := by
  have h : ((childHL (childHL (childHH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1110))) = true := by
  have h : ((childHH (childHL (childHH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf111033002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103300) = true := by
  have h : ((childHL thetaBelowCell11103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103300) h
theorem e24KC2ThetaBelowLeaf111033003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103300) = true := by
  have h : ((childHH thetaBelowCell11103300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103300) h
theorem e24KC2ThetaBelowLeaf111033012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103301) = true := by
  have h : ((childHL thetaBelowCell11103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103301) h
theorem e24KC2ThetaBelowLeaf111033013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103301) = true := by
  have h : ((childHH thetaBelowCell11103301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103301) h
theorem e24KC2ThetaBelowLeaf11103302 :
    adaptiveCoverCheck 10 thetaBelowCell11103302 = true := by
  have h : (thetaBelowCell11103302).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103302 h
theorem e24KC2ThetaBelowLeaf11103303 :
    adaptiveCoverCheck 10 thetaBelowCell11103303 = true := by
  have h : (thetaBelowCell11103303).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103303 h
theorem e24KC2ThetaBelowLeaf111033102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103310) = true := by
  have h : ((childHL thetaBelowCell11103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103310) h
theorem e24KC2ThetaBelowLeaf111033103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103310) = true := by
  have h : ((childHH thetaBelowCell11103310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103310) h
theorem e24KC2ThetaBelowLeaf111033112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11103311) = true := by
  have h : ((childHL thetaBelowCell11103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11103311) h
theorem e24KC2ThetaBelowLeaf111033113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11103311) = true := by
  have h : ((childHH thetaBelowCell11103311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11103311) h
theorem e24KC2ThetaBelowLeaf11103312 :
    adaptiveCoverCheck 10 thetaBelowCell11103312 = true := by
  have h : (thetaBelowCell11103312).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103312 h
theorem e24KC2ThetaBelowLeaf11103313 :
    adaptiveCoverCheck 10 thetaBelowCell11103313 = true := by
  have h : (thetaBelowCell11103313).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11103313 h
theorem e24KC2ThetaBelowLeaf1110332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1110))) = true := by
  have h : ((childHL (childHH (childHH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf1110333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1110))) = true := by
  have h : ((childHH (childHH (childHH thetaBelowCell1110)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH thetaBelowCell1110))) h
theorem e24KC2ThetaBelowLeaf111100 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1111)) = true := by
  have h : ((childLL (childLL thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf111101 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1111)) = true := by
  have h : ((childLH (childLL thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf1111020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL thetaBelowCell1111))) = true := by
  have h : ((childLL (childHL (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL thetaBelowCell1111))) = true := by
  have h : ((childLH (childHL (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1111))) = true := by
  have h : ((childHL (childHL (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1111))) = true := by
  have h : ((childHH (childHL (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL thetaBelowCell1111))) = true := by
  have h : ((childLL (childHH (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL thetaBelowCell1111))) = true := by
  have h : ((childLH (childHH (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1111))) = true := by
  have h : ((childHL (childHH (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1111))) = true := by
  have h : ((childHH (childHH (childLL thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf111110 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1111)) = true := by
  have h : ((childLL (childLH thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf111111 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1111)) = true := by
  have h : ((childLH (childLH thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf1111120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH thetaBelowCell1111))) = true := by
  have h : ((childLL (childHL (childLH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH thetaBelowCell1111))) = true := by
  have h : ((childLH (childHL (childLH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1111))) = true := by
  have h : ((childHL (childHL (childLH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1111))) = true := by
  have h : ((childHH (childHL (childLH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf111113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1111)) = true := by
  have h : ((childHH (childLH thetaBelowCell1111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1111)) h
theorem e24KC2ThetaBelowLeaf11112000 :
    adaptiveCoverCheck 10 thetaBelowCell11112000 = true := by
  have h : (thetaBelowCell11112000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112000 h
theorem e24KC2ThetaBelowLeaf11112001 :
    adaptiveCoverCheck 10 thetaBelowCell11112001 = true := by
  have h : (thetaBelowCell11112001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112001 h
theorem e24KC2ThetaBelowLeaf11112002 :
    adaptiveCoverCheck 10 thetaBelowCell11112002 = true := by
  have h : (thetaBelowCell11112002).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112002 h
theorem e24KC2ThetaBelowLeaf11112003 :
    adaptiveCoverCheck 10 thetaBelowCell11112003 = true := by
  have h : (thetaBelowCell11112003).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112003 h
theorem e24KC2ThetaBelowLeaf11112010 :
    adaptiveCoverCheck 10 thetaBelowCell11112010 = true := by
  have h : (thetaBelowCell11112010).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112010 h
theorem e24KC2ThetaBelowLeaf11112011 :
    adaptiveCoverCheck 10 thetaBelowCell11112011 = true := by
  have h : (thetaBelowCell11112011).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112011 h
theorem e24KC2ThetaBelowLeaf11112012 :
    adaptiveCoverCheck 10 thetaBelowCell11112012 = true := by
  have h : (thetaBelowCell11112012).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112012 h
theorem e24KC2ThetaBelowLeaf11112013 :
    adaptiveCoverCheck 10 thetaBelowCell11112013 = true := by
  have h : (thetaBelowCell11112013).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112013 h
theorem e24KC2ThetaBelowLeaf111120200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112020) = true := by
  have h : ((childLL thetaBelowCell11112020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112020) h
theorem e24KC2ThetaBelowLeaf111120201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112020) = true := by
  have h : ((childLH thetaBelowCell11112020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112020) h
theorem e24KC2ThetaBelowLeaf111120202 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112020) = true := by
  have h : ((childHL thetaBelowCell11112020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112020) h
theorem e24KC2ThetaBelowLeaf111120203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112020) = true := by
  have h : ((childHH thetaBelowCell11112020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112020) h
theorem e24KC2ThetaBelowLeaf111120210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112021) = true := by
  have h : ((childLL thetaBelowCell11112021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112021) h
theorem e24KC2ThetaBelowLeaf111120211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112021) = true := by
  have h : ((childLH thetaBelowCell11112021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112021) h
theorem e24KC2ThetaBelowLeaf111120212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112021) = true := by
  have h : ((childHL thetaBelowCell11112021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112021) h
theorem e24KC2ThetaBelowLeaf111120213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112021) = true := by
  have h : ((childHH thetaBelowCell11112021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112021) h
theorem e24KC2ThetaBelowLeaf111120300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112030) = true := by
  have h : ((childLL thetaBelowCell11112030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112030) h
theorem e24KC2ThetaBelowLeaf111120301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112030) = true := by
  have h : ((childLH thetaBelowCell11112030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112030) h
theorem e24KC2ThetaBelowLeaf111120302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112030) = true := by
  have h : ((childHL thetaBelowCell11112030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112030) h
theorem e24KC2ThetaBelowLeaf111120303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112030) = true := by
  have h : ((childHH thetaBelowCell11112030)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112030) h
theorem e24KC2ThetaBelowLeaf111120310 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112031) = true := by
  have h : ((childLL thetaBelowCell11112031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112031) h
theorem e24KC2ThetaBelowLeaf111120311 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112031) = true := by
  have h : ((childLH thetaBelowCell11112031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112031) h
theorem e24KC2ThetaBelowLeaf111120312 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112031) = true := by
  have h : ((childHL thetaBelowCell11112031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112031) h
theorem e24KC2ThetaBelowLeaf111120313 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112031) = true := by
  have h : ((childHH thetaBelowCell11112031)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112031) h
theorem e24KC2ThetaBelowLeaf11112100 :
    adaptiveCoverCheck 10 thetaBelowCell11112100 = true := by
  have h : (thetaBelowCell11112100).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112100 h
theorem e24KC2ThetaBelowLeaf11112101 :
    adaptiveCoverCheck 10 thetaBelowCell11112101 = true := by
  have h : (thetaBelowCell11112101).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112101 h
theorem e24KC2ThetaBelowLeaf11112102 :
    adaptiveCoverCheck 10 thetaBelowCell11112102 = true := by
  have h : (thetaBelowCell11112102).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112102 h
theorem e24KC2ThetaBelowLeaf11112103 :
    adaptiveCoverCheck 10 thetaBelowCell11112103 = true := by
  have h : (thetaBelowCell11112103).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112103 h
theorem e24KC2ThetaBelowLeaf11112110 :
    adaptiveCoverCheck 10 thetaBelowCell11112110 = true := by
  have h : (thetaBelowCell11112110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112110 h
theorem e24KC2ThetaBelowLeaf11112111 :
    adaptiveCoverCheck 10 thetaBelowCell11112111 = true := by
  have h : (thetaBelowCell11112111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112111 h
theorem e24KC2ThetaBelowLeaf11112112 :
    adaptiveCoverCheck 10 thetaBelowCell11112112 = true := by
  have h : (thetaBelowCell11112112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112112 h
theorem e24KC2ThetaBelowLeaf11112113 :
    adaptiveCoverCheck 10 thetaBelowCell11112113 = true := by
  have h : (thetaBelowCell11112113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112113 h
theorem e24KC2ThetaBelowLeaf111121200 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112120) = true := by
  have h : ((childLL thetaBelowCell11112120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112120) h
theorem e24KC2ThetaBelowLeaf111121201 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112120) = true := by
  have h : ((childLH thetaBelowCell11112120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112120) h
theorem e24KC2ThetaBelowLeaf111121202 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112120) = true := by
  have h : ((childHL thetaBelowCell11112120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112120) h
theorem e24KC2ThetaBelowLeaf111121203 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112120) = true := by
  have h : ((childHH thetaBelowCell11112120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112120) h
theorem e24KC2ThetaBelowLeaf111121210 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112121) = true := by
  have h : ((childLL thetaBelowCell11112121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112121) h
theorem e24KC2ThetaBelowLeaf111121211 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112121) = true := by
  have h : ((childLH thetaBelowCell11112121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112121) h
theorem e24KC2ThetaBelowLeaf111121212 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112121) = true := by
  have h : ((childHL thetaBelowCell11112121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112121) h
theorem e24KC2ThetaBelowLeaf111121213 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112121) = true := by
  have h : ((childHH thetaBelowCell11112121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112121) h
theorem e24KC2ThetaBelowLeaf111121300 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112130) = true := by
  have h : ((childLL thetaBelowCell11112130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112130) h
theorem e24KC2ThetaBelowLeaf111121301 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112130) = true := by
  have h : ((childLH thetaBelowCell11112130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112130) h
theorem e24KC2ThetaBelowLeaf111121302 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112130) = true := by
  have h : ((childHL thetaBelowCell11112130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112130) h
theorem e24KC2ThetaBelowLeaf111121303 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112130) = true := by
  have h : ((childHH thetaBelowCell11112130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112130) h
theorem e24KC2ThetaBelowLeaf11112131 :
    adaptiveCoverCheck 10 thetaBelowCell11112131 = true := by
  have h : (thetaBelowCell11112131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112131 h
theorem e24KC2ThetaBelowLeaf111121320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112132) = true := by
  have h : ((childLL thetaBelowCell11112132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112132) h
theorem e24KC2ThetaBelowLeaf111121321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112132) = true := by
  have h : ((childLH thetaBelowCell11112132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112132) h
theorem e24KC2ThetaBelowLeaf111121330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112133) = true := by
  have h : ((childLL thetaBelowCell11112133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112133) h
theorem e24KC2ThetaBelowLeaf111121331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112133) = true := by
  have h : ((childLH thetaBelowCell11112133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112133) h
theorem e24KC2ThetaBelowLeaf111122002 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112200) = true := by
  have h : ((childHL thetaBelowCell11112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112200) h
theorem e24KC2ThetaBelowLeaf111122003 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112200) = true := by
  have h : ((childHH thetaBelowCell11112200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112200) h
theorem e24KC2ThetaBelowLeaf111122012 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112201) = true := by
  have h : ((childHL thetaBelowCell11112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112201) h
theorem e24KC2ThetaBelowLeaf111122013 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112201) = true := by
  have h : ((childHH thetaBelowCell11112201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112201) h
theorem e24KC2ThetaBelowLeaf11112202 :
    adaptiveCoverCheck 10 thetaBelowCell11112202 = true := by
  have h : (thetaBelowCell11112202).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112202 h
theorem e24KC2ThetaBelowLeaf11112203 :
    adaptiveCoverCheck 10 thetaBelowCell11112203 = true := by
  have h : (thetaBelowCell11112203).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112203 h
theorem e24KC2ThetaBelowLeaf111122102 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112210) = true := by
  have h : ((childHL thetaBelowCell11112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112210) h
theorem e24KC2ThetaBelowLeaf111122103 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112210) = true := by
  have h : ((childHH thetaBelowCell11112210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112210) h
theorem e24KC2ThetaBelowLeaf111122112 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112211) = true := by
  have h : ((childHL thetaBelowCell11112211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112211) h
theorem e24KC2ThetaBelowLeaf111122120 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112212) = true := by
  have h : ((childLL thetaBelowCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112212) h
theorem e24KC2ThetaBelowLeaf111122121 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112212) = true := by
  have h : ((childLH thetaBelowCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112212) h
theorem e24KC2ThetaBelowLeaf111122122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112212) = true := by
  have h : ((childHL thetaBelowCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112212) h
theorem e24KC2ThetaBelowLeaf111122123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112212) = true := by
  have h : ((childHH thetaBelowCell11112212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112212) h
theorem e24KC2ThetaBelowLeaf111122130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112213) = true := by
  have h : ((childLL thetaBelowCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112213) h
theorem e24KC2ThetaBelowLeaf111122131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112213) = true := by
  have h : ((childLH thetaBelowCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112213) h
theorem e24KC2ThetaBelowLeaf111122132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112213) = true := by
  have h : ((childHL thetaBelowCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112213) h
theorem e24KC2ThetaBelowLeaf111122133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112213) = true := by
  have h : ((childHH thetaBelowCell11112213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112213) h
theorem e24KC2ThetaBelowLeaf11112220 :
    adaptiveCoverCheck 10 thetaBelowCell11112220 = true := by
  have h : (thetaBelowCell11112220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112220 h
theorem e24KC2ThetaBelowLeaf11112221 :
    adaptiveCoverCheck 10 thetaBelowCell11112221 = true := by
  have h : (thetaBelowCell11112221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112221 h
theorem e24KC2ThetaBelowLeaf11112222 :
    adaptiveCoverCheck 10 thetaBelowCell11112222 = true := by
  have h : (thetaBelowCell11112222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112222 h
theorem e24KC2ThetaBelowLeaf11112223 :
    adaptiveCoverCheck 10 thetaBelowCell11112223 = true := by
  have h : (thetaBelowCell11112223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112223 h
theorem e24KC2ThetaBelowLeaf11112230 :
    adaptiveCoverCheck 10 thetaBelowCell11112230 = true := by
  have h : (thetaBelowCell11112230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112230 h
theorem e24KC2ThetaBelowLeaf11112231 :
    adaptiveCoverCheck 10 thetaBelowCell11112231 = true := by
  have h : (thetaBelowCell11112231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112231 h
theorem e24KC2ThetaBelowLeaf11112232 :
    adaptiveCoverCheck 10 thetaBelowCell11112232 = true := by
  have h : (thetaBelowCell11112232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112232 h
theorem e24KC2ThetaBelowLeaf11112233 :
    adaptiveCoverCheck 10 thetaBelowCell11112233 = true := by
  have h : (thetaBelowCell11112233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112233 h
theorem e24KC2ThetaBelowLeaf111123020 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112302) = true := by
  have h : ((childLL thetaBelowCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112302) h
theorem e24KC2ThetaBelowLeaf111123021 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112302) = true := by
  have h : ((childLH thetaBelowCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112302) h
theorem e24KC2ThetaBelowLeaf111123022 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112302) = true := by
  have h : ((childHL thetaBelowCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112302) h
theorem e24KC2ThetaBelowLeaf111123023 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112302) = true := by
  have h : ((childHH thetaBelowCell11112302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112302) h
theorem e24KC2ThetaBelowLeaf111123030 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112303) = true := by
  have h : ((childLL thetaBelowCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112303) h
theorem e24KC2ThetaBelowLeaf111123031 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112303) = true := by
  have h : ((childLH thetaBelowCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112303) h
theorem e24KC2ThetaBelowLeaf111123032 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112303) = true := by
  have h : ((childHL thetaBelowCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112303) h
theorem e24KC2ThetaBelowLeaf111123033 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112303) = true := by
  have h : ((childHH thetaBelowCell11112303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112303) h
theorem e24KC2ThetaBelowLeaf111123120 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112312) = true := by
  have h : ((childLL thetaBelowCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112312) h
theorem e24KC2ThetaBelowLeaf111123121 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112312) = true := by
  have h : ((childLH thetaBelowCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112312) h
theorem e24KC2ThetaBelowLeaf111123122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112312) = true := by
  have h : ((childHL thetaBelowCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112312) h
theorem e24KC2ThetaBelowLeaf111123123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112312) = true := by
  have h : ((childHH thetaBelowCell11112312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112312) h
theorem e24KC2ThetaBelowLeaf111123130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11112313) = true := by
  have h : ((childLL thetaBelowCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11112313) h
theorem e24KC2ThetaBelowLeaf111123131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11112313) = true := by
  have h : ((childLH thetaBelowCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11112313) h
theorem e24KC2ThetaBelowLeaf111123132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11112313) = true := by
  have h : ((childHL thetaBelowCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11112313) h
theorem e24KC2ThetaBelowLeaf111123133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11112313) = true := by
  have h : ((childHH thetaBelowCell11112313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11112313) h
theorem e24KC2ThetaBelowLeaf11112320 :
    adaptiveCoverCheck 10 thetaBelowCell11112320 = true := by
  have h : (thetaBelowCell11112320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112320 h
theorem e24KC2ThetaBelowLeaf11112321 :
    adaptiveCoverCheck 10 thetaBelowCell11112321 = true := by
  have h : (thetaBelowCell11112321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112321 h
theorem e24KC2ThetaBelowLeaf11112322 :
    adaptiveCoverCheck 10 thetaBelowCell11112322 = true := by
  have h : (thetaBelowCell11112322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112322 h
theorem e24KC2ThetaBelowLeaf11112323 :
    adaptiveCoverCheck 10 thetaBelowCell11112323 = true := by
  have h : (thetaBelowCell11112323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112323 h
theorem e24KC2ThetaBelowLeaf11112330 :
    adaptiveCoverCheck 10 thetaBelowCell11112330 = true := by
  have h : (thetaBelowCell11112330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112330 h
theorem e24KC2ThetaBelowLeaf11112331 :
    adaptiveCoverCheck 10 thetaBelowCell11112331 = true := by
  have h : (thetaBelowCell11112331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112331 h
theorem e24KC2ThetaBelowLeaf11112332 :
    adaptiveCoverCheck 10 thetaBelowCell11112332 = true := by
  have h : (thetaBelowCell11112332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112332 h
theorem e24KC2ThetaBelowLeaf11112333 :
    adaptiveCoverCheck 10 thetaBelowCell11112333 = true := by
  have h : (thetaBelowCell11112333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11112333 h
theorem e24KC2ThetaBelowLeaf1111300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1111))) = true := by
  have h : ((childLL (childLL (childHH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1111))) = true := by
  have h : ((childLH (childLL (childHH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf11113020 :
    adaptiveCoverCheck 10 thetaBelowCell11113020 = true := by
  have h : (thetaBelowCell11113020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113020 h
theorem e24KC2ThetaBelowLeaf11113021 :
    adaptiveCoverCheck 10 thetaBelowCell11113021 = true := by
  have h : (thetaBelowCell11113021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113021 h
theorem e24KC2ThetaBelowLeaf111130220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113022) = true := by
  have h : ((childLL thetaBelowCell11113022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113022) h
theorem e24KC2ThetaBelowLeaf111130221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113022) = true := by
  have h : ((childLH thetaBelowCell11113022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113022) h
theorem e24KC2ThetaBelowLeaf111130230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113023) = true := by
  have h : ((childLL thetaBelowCell11113023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113023) h
theorem e24KC2ThetaBelowLeaf111130231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113023) = true := by
  have h : ((childLH thetaBelowCell11113023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113023) h
theorem e24KC2ThetaBelowLeaf11113030 :
    adaptiveCoverCheck 10 thetaBelowCell11113030 = true := by
  have h : (thetaBelowCell11113030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113030 h
theorem e24KC2ThetaBelowLeaf11113031 :
    adaptiveCoverCheck 10 thetaBelowCell11113031 = true := by
  have h : (thetaBelowCell11113031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113031 h
theorem e24KC2ThetaBelowLeaf111130320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113032) = true := by
  have h : ((childLL thetaBelowCell11113032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113032) h
theorem e24KC2ThetaBelowLeaf111130321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113032) = true := by
  have h : ((childLH thetaBelowCell11113032)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113032) h
theorem e24KC2ThetaBelowLeaf111130330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113033) = true := by
  have h : ((childLL thetaBelowCell11113033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113033) h
theorem e24KC2ThetaBelowLeaf111130331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113033) = true := by
  have h : ((childLH thetaBelowCell11113033)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113033) h
theorem e24KC2ThetaBelowLeaf1111310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1111))) = true := by
  have h : ((childLL (childLH (childHH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf1111311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1111))) = true := by
  have h : ((childLH (childLH (childHH thetaBelowCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH thetaBelowCell1111))) h
theorem e24KC2ThetaBelowLeaf11113120 :
    adaptiveCoverCheck 10 thetaBelowCell11113120 = true := by
  have h : (thetaBelowCell11113120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113120 h
theorem e24KC2ThetaBelowLeaf11113121 :
    adaptiveCoverCheck 10 thetaBelowCell11113121 = true := by
  have h : (thetaBelowCell11113121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113121 h
theorem e24KC2ThetaBelowLeaf111131220 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113122) = true := by
  have h : ((childLL thetaBelowCell11113122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113122) h
theorem e24KC2ThetaBelowLeaf111131221 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113122) = true := by
  have h : ((childLH thetaBelowCell11113122)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113122) h
theorem e24KC2ThetaBelowLeaf111131230 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113123) = true := by
  have h : ((childLL thetaBelowCell11113123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113123) h
theorem e24KC2ThetaBelowLeaf111131231 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113123) = true := by
  have h : ((childLH thetaBelowCell11113123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113123) h
theorem e24KC2ThetaBelowLeaf11113130 :
    adaptiveCoverCheck 10 thetaBelowCell11113130 = true := by
  have h : (thetaBelowCell11113130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113130 h
theorem e24KC2ThetaBelowLeaf11113131 :
    adaptiveCoverCheck 10 thetaBelowCell11113131 = true := by
  have h : (thetaBelowCell11113131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113131 h
theorem e24KC2ThetaBelowLeaf111131320 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113132) = true := by
  have h : ((childLL thetaBelowCell11113132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113132) h
theorem e24KC2ThetaBelowLeaf111131321 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113132) = true := by
  have h : ((childLH thetaBelowCell11113132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113132) h
theorem e24KC2ThetaBelowLeaf111131330 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113133) = true := by
  have h : ((childLL thetaBelowCell11113133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113133) h
theorem e24KC2ThetaBelowLeaf111131331 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113133) = true := by
  have h : ((childLH thetaBelowCell11113133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113133) h
theorem e24KC2ThetaBelowLeaf111132020 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113202) = true := by
  have h : ((childLL thetaBelowCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113202) h
theorem e24KC2ThetaBelowLeaf111132021 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113202) = true := by
  have h : ((childLH thetaBelowCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113202) h
theorem e24KC2ThetaBelowLeaf111132022 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113202) = true := by
  have h : ((childHL thetaBelowCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113202) h
theorem e24KC2ThetaBelowLeaf111132023 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113202) = true := by
  have h : ((childHH thetaBelowCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113202) h
theorem e24KC2ThetaBelowLeaf111132030 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113203) = true := by
  have h : ((childLL thetaBelowCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113203) h
theorem e24KC2ThetaBelowLeaf111132031 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113203) = true := by
  have h : ((childLH thetaBelowCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113203) h
theorem e24KC2ThetaBelowLeaf111132032 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113203) = true := by
  have h : ((childHL thetaBelowCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113203) h
theorem e24KC2ThetaBelowLeaf111132033 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113203) = true := by
  have h : ((childHH thetaBelowCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113203) h
theorem e24KC2ThetaBelowLeaf111132120 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113212) = true := by
  have h : ((childLL thetaBelowCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113212) h
theorem e24KC2ThetaBelowLeaf111132121 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113212) = true := by
  have h : ((childLH thetaBelowCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113212) h
theorem e24KC2ThetaBelowLeaf111132122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113212) = true := by
  have h : ((childHL thetaBelowCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113212) h
theorem e24KC2ThetaBelowLeaf111132123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113212) = true := by
  have h : ((childHH thetaBelowCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113212) h
theorem e24KC2ThetaBelowLeaf111132130 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113213) = true := by
  have h : ((childLL thetaBelowCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113213) h
theorem e24KC2ThetaBelowLeaf111132131 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113213) = true := by
  have h : ((childLH thetaBelowCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113213) h
theorem e24KC2ThetaBelowLeaf111132132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113213) = true := by
  have h : ((childHL thetaBelowCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113213) h
theorem e24KC2ThetaBelowLeaf111132133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113213) = true := by
  have h : ((childHH thetaBelowCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113213) h
theorem e24KC2ThetaBelowLeaf11113220 :
    adaptiveCoverCheck 10 thetaBelowCell11113220 = true := by
  have h : (thetaBelowCell11113220).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113220 h
theorem e24KC2ThetaBelowLeaf11113221 :
    adaptiveCoverCheck 10 thetaBelowCell11113221 = true := by
  have h : (thetaBelowCell11113221).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113221 h
theorem e24KC2ThetaBelowLeaf11113222 :
    adaptiveCoverCheck 10 thetaBelowCell11113222 = true := by
  have h : (thetaBelowCell11113222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113222 h
theorem e24KC2ThetaBelowLeaf11113223 :
    adaptiveCoverCheck 10 thetaBelowCell11113223 = true := by
  have h : (thetaBelowCell11113223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113223 h
theorem e24KC2ThetaBelowLeaf11113230 :
    adaptiveCoverCheck 10 thetaBelowCell11113230 = true := by
  have h : (thetaBelowCell11113230).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113230 h
theorem e24KC2ThetaBelowLeaf11113231 :
    adaptiveCoverCheck 10 thetaBelowCell11113231 = true := by
  have h : (thetaBelowCell11113231).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113231 h
theorem e24KC2ThetaBelowLeaf11113232 :
    adaptiveCoverCheck 10 thetaBelowCell11113232 = true := by
  have h : (thetaBelowCell11113232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113232 h
theorem e24KC2ThetaBelowLeaf11113233 :
    adaptiveCoverCheck 10 thetaBelowCell11113233 = true := by
  have h : (thetaBelowCell11113233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113233 h
theorem e24KC2ThetaBelowLeaf111133020 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113302) = true := by
  have h : ((childLL thetaBelowCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113302) h
theorem e24KC2ThetaBelowLeaf111133021 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113302) = true := by
  have h : ((childLH thetaBelowCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113302) h
theorem e24KC2ThetaBelowLeaf111133022 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113302) = true := by
  have h : ((childHL thetaBelowCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113302) h
theorem e24KC2ThetaBelowLeaf111133023 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113302) = true := by
  have h : ((childHH thetaBelowCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113302) h
theorem e24KC2ThetaBelowLeaf111133030 :
    adaptiveCoverCheck 9 (childLL thetaBelowCell11113303) = true := by
  have h : ((childLL thetaBelowCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL thetaBelowCell11113303) h
theorem e24KC2ThetaBelowLeaf111133031 :
    adaptiveCoverCheck 9 (childLH thetaBelowCell11113303) = true := by
  have h : ((childLH thetaBelowCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH thetaBelowCell11113303) h
theorem e24KC2ThetaBelowLeaf111133032 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113303) = true := by
  have h : ((childHL thetaBelowCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113303) h
theorem e24KC2ThetaBelowLeaf111133033 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113303) = true := by
  have h : ((childHH thetaBelowCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113303) h
theorem e24KC2ThetaBelowLeaf111133122 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113312) = true := by
  have h : ((childHL thetaBelowCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113312) h
theorem e24KC2ThetaBelowLeaf111133123 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113312) = true := by
  have h : ((childHH thetaBelowCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113312) h
theorem e24KC2ThetaBelowLeaf111133132 :
    adaptiveCoverCheck 9 (childHL thetaBelowCell11113313) = true := by
  have h : ((childHL thetaBelowCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL thetaBelowCell11113313) h
theorem e24KC2ThetaBelowLeaf111133133 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113313) = true := by
  have h : ((childHH thetaBelowCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH thetaBelowCell11113313) h
theorem e24KC2ThetaBelowLeaf11113320 :
    adaptiveCoverCheck 10 thetaBelowCell11113320 = true := by
  have h : (thetaBelowCell11113320).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113320 h
theorem e24KC2ThetaBelowLeaf11113321 :
    adaptiveCoverCheck 10 thetaBelowCell11113321 = true := by
  have h : (thetaBelowCell11113321).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113321 h
theorem e24KC2ThetaBelowLeaf11113322 :
    adaptiveCoverCheck 10 thetaBelowCell11113322 = true := by
  have h : (thetaBelowCell11113322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113322 h
theorem e24KC2ThetaBelowLeaf11113323 :
    adaptiveCoverCheck 10 thetaBelowCell11113323 = true := by
  have h : (thetaBelowCell11113323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113323 h
theorem e24KC2ThetaBelowLeaf11113330 :
    adaptiveCoverCheck 10 thetaBelowCell11113330 = true := by
  have h : (thetaBelowCell11113330).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113330 h
theorem e24KC2ThetaBelowLeaf11113331 :
    adaptiveCoverCheck 10 thetaBelowCell11113331 = true := by
  have h : (thetaBelowCell11113331).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113331 h
theorem e24KC2ThetaBelowLeaf11113332 :
    adaptiveCoverCheck 10 thetaBelowCell11113332 = true := by
  have h : (thetaBelowCell11113332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113332 h
theorem e24KC2ThetaBelowLeaf11113333 :
    adaptiveCoverCheck 10 thetaBelowCell11113333 = true := by
  have h : (thetaBelowCell11113333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell11113333 h
theorem e24KC2ThetaBelowLeaf111200 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1112)) = true := by
  have h : ((childLL (childLL thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf111201 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1112)) = true := by
  have h : ((childLH (childLL thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf111202 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1112)) = true := by
  have h : ((childHL (childLL thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf111203 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1112)) = true := by
  have h : ((childHH (childLL thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf1112100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH thetaBelowCell1112))) = true := by
  have h : ((childLL (childLL (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH thetaBelowCell1112))) = true := by
  have h : ((childLH (childLL (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH thetaBelowCell1112))) = true := by
  have h : ((childHL (childLL (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH thetaBelowCell1112))) = true := by
  have h : ((childHH (childLL (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH thetaBelowCell1112))) = true := by
  have h : ((childLL (childLH (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH thetaBelowCell1112))) = true := by
  have h : ((childLH (childLH (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH thetaBelowCell1112))) = true := by
  have h : ((childHL (childLH (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf1112113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH thetaBelowCell1112))) = true := by
  have h : ((childHH (childLH (childLH thetaBelowCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH thetaBelowCell1112))) h
theorem e24KC2ThetaBelowLeaf111212 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1112)) = true := by
  have h : ((childHL (childLH thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf111213 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1112)) = true := by
  have h : ((childHH (childLH thetaBelowCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1112)) h
theorem e24KC2ThetaBelowLeaf11122 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1112) = true := by
  have h : ((childHL thetaBelowCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1112) h
theorem e24KC2ThetaBelowLeaf11123 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1112) = true := by
  have h : ((childHH thetaBelowCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1112) h
theorem e24KC2ThetaBelowLeaf1113000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL thetaBelowCell1113))) = true := by
  have h : ((childLL (childLL (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL thetaBelowCell1113))) = true := by
  have h : ((childLH (childLL (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL thetaBelowCell1113))) = true := by
  have h : ((childHL (childLL (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL thetaBelowCell1113))) = true := by
  have h : ((childHH (childLL (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL thetaBelowCell1113))) = true := by
  have h : ((childLL (childLH (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL thetaBelowCell1113))) = true := by
  have h : ((childLH (childLH (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL thetaBelowCell1113))) = true := by
  have h : ((childHL (childLH (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL thetaBelowCell1113))) = true := by
  have h : ((childHH (childLH (childLL thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLL thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf111302 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1113)) = true := by
  have h : ((childHL (childLL thetaBelowCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1113)) h
theorem e24KC2ThetaBelowLeaf111303 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1113)) = true := by
  have h : ((childHH (childLL thetaBelowCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1113)) h
theorem e24KC2ThetaBelowLeaf1113100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH thetaBelowCell1113))) = true := by
  have h : ((childLL (childLL (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH thetaBelowCell1113))) = true := by
  have h : ((childLH (childLL (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH thetaBelowCell1113))) = true := by
  have h : ((childHL (childLL (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH thetaBelowCell1113))) = true := by
  have h : ((childHH (childLL (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH thetaBelowCell1113))) = true := by
  have h : ((childLL (childLH (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH thetaBelowCell1113))) = true := by
  have h : ((childLH (childLH (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH thetaBelowCell1113))) = true := by
  have h : ((childHL (childLH (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf1113113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH thetaBelowCell1113))) = true := by
  have h : ((childHH (childLH (childLH thetaBelowCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH thetaBelowCell1113))) h
theorem e24KC2ThetaBelowLeaf111312 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1113)) = true := by
  have h : ((childHL (childLH thetaBelowCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1113)) h
theorem e24KC2ThetaBelowLeaf111313 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1113)) = true := by
  have h : ((childHH (childLH thetaBelowCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1113)) h
theorem e24KC2ThetaBelowLeaf11132 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1113) = true := by
  have h : ((childHL thetaBelowCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1113) h
theorem e24KC2ThetaBelowLeaf11133 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1113) = true := by
  have h : ((childHH thetaBelowCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1113) h
theorem e24KC2ThetaBelowLeaf1120 :
    adaptiveCoverCheck 14 thetaBelowCell1120 = true := by
  have h : (thetaBelowCell1120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1120 h
theorem e24KC2ThetaBelowLeaf11210 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1121) = true := by
  have h : ((childLL thetaBelowCell1121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1121) h
theorem e24KC2ThetaBelowLeaf11211 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1121) = true := by
  have h : ((childLH thetaBelowCell1121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell1121) h
theorem e24KC2ThetaBelowLeaf11212 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1121) = true := by
  have h : ((childHL thetaBelowCell1121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1121) h
theorem e24KC2ThetaBelowLeaf11213 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1121) = true := by
  have h : ((childHH thetaBelowCell1121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1121) h
theorem e24KC2ThetaBelowLeaf1122 :
    adaptiveCoverCheck 14 thetaBelowCell1122 = true := by
  have h : (thetaBelowCell1122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1122 h
theorem e24KC2ThetaBelowLeaf1123 :
    adaptiveCoverCheck 14 thetaBelowCell1123 = true := by
  have h : (thetaBelowCell1123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1123 h
theorem e24KC2ThetaBelowLeaf11300 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1130) = true := by
  have h : ((childLL thetaBelowCell1130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1130) h
theorem e24KC2ThetaBelowLeaf11301 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1130) = true := by
  have h : ((childLH thetaBelowCell1130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell1130) h
theorem e24KC2ThetaBelowLeaf11302 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1130) = true := by
  have h : ((childHL thetaBelowCell1130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1130) h
theorem e24KC2ThetaBelowLeaf11303 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1130) = true := by
  have h : ((childHH thetaBelowCell1130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1130) h
theorem e24KC2ThetaBelowLeaf11310 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1131) = true := by
  have h : ((childLL thetaBelowCell1131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1131) h
theorem e24KC2ThetaBelowLeaf11311 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1131) = true := by
  have h : ((childLH thetaBelowCell1131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell1131) h
theorem e24KC2ThetaBelowLeaf11312 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1131) = true := by
  have h : ((childHL thetaBelowCell1131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1131) h
theorem e24KC2ThetaBelowLeaf11313 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1131) = true := by
  have h : ((childHH thetaBelowCell1131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1131) h
theorem e24KC2ThetaBelowLeaf1132 :
    adaptiveCoverCheck 14 thetaBelowCell1132 = true := by
  have h : (thetaBelowCell1132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1132 h
theorem e24KC2ThetaBelowLeaf1133 :
    adaptiveCoverCheck 14 thetaBelowCell1133 = true := by
  have h : (thetaBelowCell1133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1133 h
theorem e24KC2ThetaBelowLeaf120 :
    adaptiveCoverCheck 15 (childLL (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHL (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf121 :
    adaptiveCoverCheck 15 (childLH (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHL (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf122 :
    adaptiveCoverCheck 15 (childHL (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHL (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHL (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf123 :
    adaptiveCoverCheck 15 (childHH (childHL (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childHL (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHL (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf1300 :
    adaptiveCoverCheck 14 thetaBelowCell1300 = true := by
  have h : (thetaBelowCell1300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1300 h
theorem e24KC2ThetaBelowLeaf1301 :
    adaptiveCoverCheck 14 thetaBelowCell1301 = true := by
  have h : (thetaBelowCell1301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1301 h
theorem e24KC2ThetaBelowLeaf1302 :
    adaptiveCoverCheck 14 thetaBelowCell1302 = true := by
  have h : (thetaBelowCell1302).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1302 h
theorem e24KC2ThetaBelowLeaf1303 :
    adaptiveCoverCheck 14 thetaBelowCell1303 = true := by
  have h : (thetaBelowCell1303).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1303 h
theorem e24KC2ThetaBelowLeaf1310 :
    adaptiveCoverCheck 14 thetaBelowCell1310 = true := by
  have h : (thetaBelowCell1310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1310 h
theorem e24KC2ThetaBelowLeaf1311 :
    adaptiveCoverCheck 14 thetaBelowCell1311 = true := by
  have h : (thetaBelowCell1311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1311 h
theorem e24KC2ThetaBelowLeaf1312 :
    adaptiveCoverCheck 14 thetaBelowCell1312 = true := by
  have h : (thetaBelowCell1312).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1312 h
theorem e24KC2ThetaBelowLeaf1313 :
    adaptiveCoverCheck 14 thetaBelowCell1313 = true := by
  have h : (thetaBelowCell1313).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1313 h
theorem e24KC2ThetaBelowLeaf132 :
    adaptiveCoverCheck 15 (childHL (childHH (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHL (childHH (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childHH (childLH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf133 :
    adaptiveCoverCheck 15 (childHH (childHH (childLH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childHH (childLH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHH (childLH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf2 :
    adaptiveCoverCheck 17 (childHL e24ThetaBelowRoot) = true := by
  have h : physicallyIrrelevant (childHL e24ThetaBelowRoot) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 17 (childHL e24ThetaBelowRoot) h
theorem e24KC2ThetaBelowLeaf300 :
    adaptiveCoverCheck 15 (childLL (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childLL (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childLL (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf301 :
    adaptiveCoverCheck 15 (childLH (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childLL (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childLL (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf302 :
    adaptiveCoverCheck 15 (childHL (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childLL (childHH
    e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf303 :
    adaptiveCoverCheck 15 (childHH (childLL (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childLL (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childLL (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf310 :
    adaptiveCoverCheck 15 (childLL (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childLH (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf311 :
    adaptiveCoverCheck 15 (childLH (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childLH (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf312 :
    adaptiveCoverCheck 15 (childHL (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childHL (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHL (childLH (childHH e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf313 :
    adaptiveCoverCheck 15 (childHH (childLH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childLH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childLH (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf32 :
    adaptiveCoverCheck 16 (childHL (childHH e24ThetaBelowRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childHH e24ThetaBelowRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 16 (childHL (childHH e24ThetaBelowRoot)) h

theorem e24KC2ThetaBelowLeaf330 :
    adaptiveCoverCheck 15 (childLL (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childLL (childHH (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childLL (childHH (childHH
    e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf331 :
    adaptiveCoverCheck 15 (childLH (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childHH (childHH e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHH (childHH e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf332 :
    adaptiveCoverCheck 15 (childHL (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childHH (childHH
    e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf333 :
    adaptiveCoverCheck 15 (childHH (childHH (childHH e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHH (childHH (childHH e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHH (childHH (childHH
    e24ThetaBelowRoot))) h

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

* `KernelOnly.PartE.E24KC6ProofBatch38ee6acacaee22e4`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc9f578345f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc9f578345f

open CertificateCellsc9f578345f
theorem cover_subtree_27436d0eee02 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022003100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003100)
    (by
      have h : ((childLL (childLL thetaAboveCell000022003100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL thetaAboveCell000022003100)) h)
    (by
      have h : ((childLH (childLL thetaAboveCell000022003100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL thetaAboveCell000022003100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022003100))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022003100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022003100))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022003100))) h))

theorem cover_subtree_3bcbb01846ea :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022003100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003100)
    (by
      have h : ((childLL (childLH thetaAboveCell000022003100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH thetaAboveCell000022003100)) h)
    (by
      have h : ((childLH (childLH thetaAboveCell000022003100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH thetaAboveCell000022003100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022003100))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022003100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022003100))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022003100))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022003100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022003100))) h))

theorem cover_subtree_ffb85ef67591 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002020
        (by
          have h : ((childLL thetaAboveCell0000220031002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002020) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002020) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002020) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002021
        (by
          have h : ((childLL thetaAboveCell0000220031002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002021) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002021) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002021) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002022
        (by
          have h : ((childLL thetaAboveCell0000220031002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002022) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002022) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002022) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002023
        (by
          have h : ((childLL thetaAboveCell0000220031002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002023) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002023) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002023) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002023) h))

theorem cover_subtree_86bc98112499 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002030
        (by
          have h : ((childLL thetaAboveCell0000220031002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002030) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002030) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002030) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002031
        (by
          have h : ((childLL thetaAboveCell0000220031002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002031) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002031) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002031) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002032
        (by
          have h : ((childLL thetaAboveCell0000220031002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002032) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002032) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002032) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002033
        (by
          have h : ((childLL thetaAboveCell0000220031002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002033) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002033) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002033) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002033) h))

theorem cover_subtree_7cd81c60142e :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022003100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022003100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031002000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002000 h)
        (by
          have h : (thetaAboveCell0000220031002001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002001 h)
        (by
          have h : (thetaAboveCell0000220031002002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002002 h)
        (by
          have h : (thetaAboveCell0000220031002003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031002010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002010 h)
        (by
          have h : (thetaAboveCell0000220031002011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002011 h)
        (by
          have h : (thetaAboveCell0000220031002012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002012 h)
        (by
          have h : (thetaAboveCell0000220031002013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002013 h))
    cover_subtree_ffb85ef67591
    cover_subtree_86bc98112499

theorem cover_subtree_5fb03cd03eba :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002120
        (by
          have h : ((childLL thetaAboveCell0000220031002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002120) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002120) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002120) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002121
        (by
          have h : ((childLL thetaAboveCell0000220031002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002121) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002121) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002121) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002122
        (by
          have h : ((childLL thetaAboveCell0000220031002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002122) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002122) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002122) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002123
        (by
          have h : ((childLL thetaAboveCell0000220031002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002123) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002123) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002123) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002123) h))

theorem cover_subtree_4ea44b529295 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002130
        (by
          have h : ((childLL thetaAboveCell0000220031002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002130) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002130) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002130) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002131
        (by
          have h : ((childLL thetaAboveCell0000220031002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002131) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002131) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002131) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002132
        (by
          have h : ((childLL thetaAboveCell0000220031002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002132) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002132) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002132) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002133
        (by
          have h : ((childLL thetaAboveCell0000220031002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002133) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002133) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002133) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002133) h))

theorem cover_subtree_db4866b2cd56 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022003100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022003100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031002100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002100 h)
        (by
          have h : (thetaAboveCell0000220031002101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002101 h)
        (by
          have h : (thetaAboveCell0000220031002102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002102 h)
        (by
          have h : (thetaAboveCell0000220031002103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031002110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002110 h)
        (by
          have h : (thetaAboveCell0000220031002111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002111 h)
        (by
          have h : (thetaAboveCell0000220031002112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002112 h)
        (by
          have h : (thetaAboveCell0000220031002113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002113 h))
    cover_subtree_5fb03cd03eba
    cover_subtree_4ea44b529295

theorem cover_subtree_da1ce2a1ea10 :
    adaptiveCoverCheck 4 (childLL (childHL (childHL thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002200
        (by
          have h : ((childLL thetaAboveCell0000220031002200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002200) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002200) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002200) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002200)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002200) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002201
        (by
          have h : ((childLL thetaAboveCell0000220031002201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002201) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002201) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002201) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002201)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002201) h))
    (by
      have h : (thetaAboveCell0000220031002202).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002202 h)
    (by
      have h : (thetaAboveCell0000220031002203).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002203 h)

theorem cover_subtree_ea6d149e7e1e :
    adaptiveCoverCheck 4 (childLH (childHL (childHL thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002210
        (by
          have h : ((childLL thetaAboveCell0000220031002210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002210) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002210) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002210) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002210)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002210) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002211
        (by
          have h : ((childLL thetaAboveCell0000220031002211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002211) h)
        (by
          have h : ((childLH thetaAboveCell0000220031002211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002211) h)
        (by
          have h : ((childHL thetaAboveCell0000220031002211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002211) h)
        (by
          have h : ((childHH thetaAboveCell0000220031002211)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002211) h))
    (by
      have h : (thetaAboveCell0000220031002212).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002212 h)
    (by
      have h : (thetaAboveCell0000220031002213).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002213 h)

theorem cover_subtree_5106e0b16eef :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022003100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022003100))
    cover_subtree_da1ce2a1ea10
    cover_subtree_ea6d149e7e1e
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022003100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022003100))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022003100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022003100))) h)

theorem cover_subtree_a4e3e0266d1a :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022003100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022003100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022003100)))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031002300
            (by
              have h : ((childLL thetaAboveCell0000220031002300)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031002300)
                h)
            (by
              have h : ((childLH thetaAboveCell0000220031002300)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031002300)
                h)
            (by
              have h : ((childHL thetaAboveCell0000220031002300)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031002300)
                h)
            (by
              have h : ((childHH thetaAboveCell0000220031002300)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031002300)
                h))
        (by
          have h : (thetaAboveCell0000220031002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002301 h)
        (by
          have h : (thetaAboveCell0000220031002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002302 h)
        (by
          have h : (thetaAboveCell0000220031002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002310 h)
        (by
          have h : (thetaAboveCell0000220031002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002311 h)
        (by
          have h : (thetaAboveCell0000220031002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002312 h)
        (by
          have h : (thetaAboveCell0000220031002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022003100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022003100))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022003100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022003100))) h)

theorem cover_subtree_e3fd3e08cd04 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022003100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022003100)
    cover_subtree_7cd81c60142e
    cover_subtree_db4866b2cd56
    cover_subtree_5106e0b16eef
    cover_subtree_a4e3e0266d1a

theorem cover_subtree_fed900b890f0 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003020
        (by
          have h : ((childLL thetaAboveCell0000220031003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003020) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003020) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003020) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003021
        (by
          have h : ((childLL thetaAboveCell0000220031003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003021) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003021) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003021) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003022
        (by
          have h : ((childLL thetaAboveCell0000220031003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003022) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003022) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003022) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003023
        (by
          have h : ((childLL thetaAboveCell0000220031003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003023) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003023) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003023) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003023) h))

theorem cover_subtree_f5a67bd75b07 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003030
        (by
          have h : ((childLL thetaAboveCell0000220031003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003030) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003030) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003030) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003031
        (by
          have h : ((childLL thetaAboveCell0000220031003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003031) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003031) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003031) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003032
        (by
          have h : ((childLL thetaAboveCell0000220031003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003032) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003032) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003032) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003033
        (by
          have h : ((childLL thetaAboveCell0000220031003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003033) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003033) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003033) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003033) h))

theorem cover_subtree_dc2ce2de1a67 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022003100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022003100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031003000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003000 h)
        (by
          have h : (thetaAboveCell0000220031003001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003001 h)
        (by
          have h : (thetaAboveCell0000220031003002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003002 h)
        (by
          have h : (thetaAboveCell0000220031003003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031003010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003010 h)
        (by
          have h : (thetaAboveCell0000220031003011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003011 h)
        (by
          have h : (thetaAboveCell0000220031003012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003012 h)
        (by
          have h : (thetaAboveCell0000220031003013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003013 h))
    cover_subtree_fed900b890f0
    cover_subtree_f5a67bd75b07

theorem cover_subtree_ecb8f710d653 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003120
        (by
          have h : ((childLL thetaAboveCell0000220031003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003120) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003120) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003120) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003121
        (by
          have h : ((childLL thetaAboveCell0000220031003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003121) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003121) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003121) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003122
        (by
          have h : ((childLL thetaAboveCell0000220031003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003122) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003122) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003122) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003123
        (by
          have h : ((childLL thetaAboveCell0000220031003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003123) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003123) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003123) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003123) h))

theorem cover_subtree_0f60a6ff8480 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022003100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022003100)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003130
        (by
          have h : ((childLL thetaAboveCell0000220031003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003130) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003130) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003130) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003131
        (by
          have h : ((childLL thetaAboveCell0000220031003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003131) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003131) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003131) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003132
        (by
          have h : ((childLL thetaAboveCell0000220031003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003132) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003132) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003132) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031003133
        (by
          have h : ((childLL thetaAboveCell0000220031003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031003133) h)
        (by
          have h : ((childLH thetaAboveCell0000220031003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031003133) h)
        (by
          have h : ((childHL thetaAboveCell0000220031003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031003133) h)
        (by
          have h : ((childHH thetaAboveCell0000220031003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031003133) h))

theorem cover_subtree_12980021aa15 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022003100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022003100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031003100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003100 h)
        (by
          have h : (thetaAboveCell0000220031003101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003101 h)
        (by
          have h : (thetaAboveCell0000220031003102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003102 h)
        (by
          have h : (thetaAboveCell0000220031003103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031003110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003110 h)
        (by
          have h : (thetaAboveCell0000220031003111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003111 h)
        (by
          have h : (thetaAboveCell0000220031003112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003112 h)
        (by
          have h : (thetaAboveCell0000220031003113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003113 h))
    cover_subtree_ecb8f710d653
    cover_subtree_0f60a6ff8480

theorem cover_subtree_96b385ccf927 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022003100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022003100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003200 h)
        (by
          have h : (thetaAboveCell0000220031003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003201 h)
        (by
          have h : (thetaAboveCell0000220031003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003202 h)
        (by
          have h : (thetaAboveCell0000220031003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003210 h)
        (by
          have h : (thetaAboveCell0000220031003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003211 h)
        (by
          have h : (thetaAboveCell0000220031003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003212 h)
        (by
          have h : (thetaAboveCell0000220031003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022003100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022003100))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022003100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022003100))) h)

theorem cover_subtree_22b398081cb0 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022003100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022003100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003300 h)
        (by
          have h : (thetaAboveCell0000220031003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003301 h)
        (by
          have h : (thetaAboveCell0000220031003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003302 h)
        (by
          have h : (thetaAboveCell0000220031003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022003100)))
        (by
          have h : (thetaAboveCell0000220031003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003310 h)
        (by
          have h : (thetaAboveCell0000220031003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003311 h)
        (by
          have h : (thetaAboveCell0000220031003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003312 h)
        (by
          have h : (thetaAboveCell0000220031003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022003100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022003100))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022003100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022003100))) h)

theorem cover_subtree_b9c469e743af :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022003100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022003100)
    cover_subtree_dc2ce2de1a67
    cover_subtree_12980021aa15
    cover_subtree_96b385ccf927
    cover_subtree_22b398081cb0

theorem cover_subtree_2d90eed026dd :
    adaptiveCoverCheck 7 thetaAboveCell000022003100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003100
    cover_subtree_27436d0eee02
    cover_subtree_3bcbb01846ea
    cover_subtree_e3fd3e08cd04
    cover_subtree_b9c469e743af

theorem cover_subtree_e582f747675b :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022003101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022003101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012020
        (by
          have h : ((childLL thetaAboveCell0000220031012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012020) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012020) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012020) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012021
        (by
          have h : ((childLL thetaAboveCell0000220031012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012021) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012021) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012021) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012022
        (by
          have h : ((childLL thetaAboveCell0000220031012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012022) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012022) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012022) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012023
        (by
          have h : ((childLL thetaAboveCell0000220031012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012023) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012023) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012023) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012023) h))

theorem cover_subtree_9833e059fd15 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022003101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022003101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012030
        (by
          have h : ((childLL thetaAboveCell0000220031012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012030) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012030) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012030) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012031
        (by
          have h : ((childLL thetaAboveCell0000220031012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012031) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012031) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012031) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012032
        (by
          have h : ((childLL thetaAboveCell0000220031012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012032) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012032) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012032) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012032) h))
    (by
      have h : (thetaAboveCell0000220031012033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012033 h)

theorem cover_subtree_f35cbab27ebd :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022003101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022003101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031012000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012000 h)
        (by
          have h : (thetaAboveCell0000220031012001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012001 h)
        (by
          have h : (thetaAboveCell0000220031012002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012002 h)
        (by
          have h : (thetaAboveCell0000220031012003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031012010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012010 h)
        (by
          have h : (thetaAboveCell0000220031012011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012011 h)
        (by
          have h : (thetaAboveCell0000220031012012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012012 h)
        (by
          have h : (thetaAboveCell0000220031012013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012013 h))
    cover_subtree_e582f747675b
    cover_subtree_9833e059fd15

theorem cover_subtree_4567a99abbdc :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022003101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022003101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012120
        (by
          have h : ((childLL thetaAboveCell0000220031012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012120) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012120) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012120) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012121
        (by
          have h : ((childLL thetaAboveCell0000220031012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012121) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012121) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012121) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012121) h))
    (by
      have h : (thetaAboveCell0000220031012122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012122 h)
    (by
      have h : (thetaAboveCell0000220031012123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012123 h)

theorem cover_subtree_7c0ef6ceebf5 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022003101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022003101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012130
        (by
          have h : ((childLL thetaAboveCell0000220031012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012130) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012130) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012130) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031012131
        (by
          have h : ((childLL thetaAboveCell0000220031012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031012131) h)
        (by
          have h : ((childLH thetaAboveCell0000220031012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031012131) h)
        (by
          have h : ((childHL thetaAboveCell0000220031012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031012131) h)
        (by
          have h : ((childHH thetaAboveCell0000220031012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031012131) h))
    (by
      have h : (thetaAboveCell0000220031012132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012132 h)
    (by
      have h : (thetaAboveCell0000220031012133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012133 h)

theorem cover_subtree_8358923d8e75 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022003101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022003101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031012100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012100 h)
        (by
          have h : (thetaAboveCell0000220031012101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012101 h)
        (by
          have h : (thetaAboveCell0000220031012102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012102 h)
        (by
          have h : (thetaAboveCell0000220031012103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031012110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012110 h)
        (by
          have h : (thetaAboveCell0000220031012111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012111 h)
        (by
          have h : (thetaAboveCell0000220031012112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012112 h)
        (by
          have h : (thetaAboveCell0000220031012113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012113 h))
    cover_subtree_4567a99abbdc
    cover_subtree_7c0ef6ceebf5

theorem cover_subtree_d6a0244cc9dc :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022003101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022003101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012200 h)
        (by
          have h : (thetaAboveCell0000220031012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012201 h)
        (by
          have h : (thetaAboveCell0000220031012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012202 h)
        (by
          have h : (thetaAboveCell0000220031012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012210 h)
        (by
          have h : (thetaAboveCell0000220031012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012211 h)
        (by
          have h : (thetaAboveCell0000220031012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012212 h)
        (by
          have h : (thetaAboveCell0000220031012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022003101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022003101))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022003101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022003101))) h)

theorem cover_subtree_0a6d165e5f89 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022003101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022003101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012300 h)
        (by
          have h : (thetaAboveCell0000220031012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012301 h)
        (by
          have h : (thetaAboveCell0000220031012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012302 h)
        (by
          have h : (thetaAboveCell0000220031012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012310 h)
        (by
          have h : (thetaAboveCell0000220031012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012311 h)
        (by
          have h : (thetaAboveCell0000220031012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012312 h)
        (by
          have h : (thetaAboveCell0000220031012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022003101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022003101))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022003101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022003101))) h)

theorem cover_subtree_0b78493a586a :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022003101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022003101)
    cover_subtree_f35cbab27ebd
    cover_subtree_8358923d8e75
    cover_subtree_d6a0244cc9dc
    cover_subtree_0a6d165e5f89

theorem cover_subtree_57ad90623a2b :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022003101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022003101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031013020
        (by
          have h : ((childLL thetaAboveCell0000220031013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031013020) h)
        (by
          have h : ((childLH thetaAboveCell0000220031013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031013020) h)
        (by
          have h : ((childHL thetaAboveCell0000220031013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031013020) h)
        (by
          have h : ((childHH thetaAboveCell0000220031013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031013020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031013021
        (by
          have h : ((childLL thetaAboveCell0000220031013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031013021) h)
        (by
          have h : ((childLH thetaAboveCell0000220031013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031013021) h)
        (by
          have h : ((childHL thetaAboveCell0000220031013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031013021) h)
        (by
          have h : ((childHH thetaAboveCell0000220031013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031013021) h))
    (by
      have h : (thetaAboveCell0000220031013022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013022 h)
    (by
      have h : (thetaAboveCell0000220031013023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013023 h)

theorem cover_subtree_cab424cfd961 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022003101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022003101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031013030
        (by
          have h : ((childLL thetaAboveCell0000220031013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031013030) h)
        (by
          have h : ((childLH thetaAboveCell0000220031013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031013030) h)
        (by
          have h : ((childHL thetaAboveCell0000220031013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031013030) h)
        (by
          have h : ((childHH thetaAboveCell0000220031013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031013030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031013031
        (by
          have h : ((childLL thetaAboveCell0000220031013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031013031) h)
        (by
          have h : ((childLH thetaAboveCell0000220031013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031013031) h)
        (by
          have h : ((childHL thetaAboveCell0000220031013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031013031) h)
        (by
          have h : ((childHH thetaAboveCell0000220031013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031013031) h))
    (by
      have h : (thetaAboveCell0000220031013032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013032 h)
    (by
      have h : (thetaAboveCell0000220031013033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013033 h)

theorem cover_subtree_af6ea412af3a :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022003101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022003101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031013000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013000 h)
        (by
          have h : (thetaAboveCell0000220031013001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013001 h)
        (by
          have h : (thetaAboveCell0000220031013002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013002 h)
        (by
          have h : (thetaAboveCell0000220031013003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031013010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013010 h)
        (by
          have h : (thetaAboveCell0000220031013011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013011 h)
        (by
          have h : (thetaAboveCell0000220031013012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013012 h)
        (by
          have h : (thetaAboveCell0000220031013013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013013 h))
    cover_subtree_57ad90623a2b
    cover_subtree_cab424cfd961

theorem cover_subtree_ab0d022d0753 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022003101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022003101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031013120
        (by
          have h : ((childLL thetaAboveCell0000220031013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031013120) h)
        (by
          have h : ((childLH thetaAboveCell0000220031013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031013120) h)
        (by
          have h : ((childHL thetaAboveCell0000220031013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031013120) h)
        (by
          have h : ((childHH thetaAboveCell0000220031013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031013120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031013121
        (by
          have h : ((childLL thetaAboveCell0000220031013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031013121) h)
        (by
          have h : ((childLH thetaAboveCell0000220031013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031013121) h)
        (by
          have h : ((childHL thetaAboveCell0000220031013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031013121) h)
        (by
          have h : ((childHH thetaAboveCell0000220031013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031013121) h))
    (by
      have h : (thetaAboveCell0000220031013122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013122 h)
    (by
      have h : (thetaAboveCell0000220031013123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013123 h)

theorem cover_subtree_6515bfe621d1 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022003101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022003101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031013130
        (by
          have h : ((childLL thetaAboveCell0000220031013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031013130) h)
        (by
          have h : ((childLH thetaAboveCell0000220031013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031013130) h)
        (by
          have h : ((childHL thetaAboveCell0000220031013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031013130) h)
        (by
          have h : ((childHH thetaAboveCell0000220031013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031013130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031013131
        (by
          have h : ((childLL thetaAboveCell0000220031013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031013131) h)
        (by
          have h : ((childLH thetaAboveCell0000220031013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031013131) h)
        (by
          have h : ((childHL thetaAboveCell0000220031013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031013131) h)
        (by
          have h : ((childHH thetaAboveCell0000220031013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031013131) h))
    (by
      have h : (thetaAboveCell0000220031013132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013132 h)
    (by
      have h : (thetaAboveCell0000220031013133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013133 h)

theorem cover_subtree_9d368eedb456 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022003101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022003101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031013100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013100 h)
        (by
          have h : (thetaAboveCell0000220031013101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013101 h)
        (by
          have h : (thetaAboveCell0000220031013102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013102 h)
        (by
          have h : (thetaAboveCell0000220031013103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031013110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013110 h)
        (by
          have h : (thetaAboveCell0000220031013111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013111 h)
        (by
          have h : (thetaAboveCell0000220031013112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013112 h)
        (by
          have h : (thetaAboveCell0000220031013113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013113 h))
    cover_subtree_ab0d022d0753
    cover_subtree_6515bfe621d1

theorem cover_subtree_a19642467be9 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022003101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022003101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013200 h)
        (by
          have h : (thetaAboveCell0000220031013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013201 h)
        (by
          have h : (thetaAboveCell0000220031013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013202 h)
        (by
          have h : (thetaAboveCell0000220031013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013210 h)
        (by
          have h : (thetaAboveCell0000220031013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013211 h)
        (by
          have h : (thetaAboveCell0000220031013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013212 h)
        (by
          have h : (thetaAboveCell0000220031013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022003101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022003101))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022003101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022003101))) h)

theorem cover_subtree_6b1d70907da0 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022003101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022003101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013300 h)
        (by
          have h : (thetaAboveCell0000220031013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013301 h)
        (by
          have h : (thetaAboveCell0000220031013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013302 h)
        (by
          have h : (thetaAboveCell0000220031013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022003101)))
        (by
          have h : (thetaAboveCell0000220031013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013310 h)
        (by
          have h : (thetaAboveCell0000220031013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013311 h)
        (by
          have h : (thetaAboveCell0000220031013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013312 h)
        (by
          have h : (thetaAboveCell0000220031013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031013313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022003101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022003101))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022003101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022003101))) h)

theorem cover_subtree_e3814f5f5798 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022003101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022003101)
    cover_subtree_af6ea412af3a
    cover_subtree_9d368eedb456
    cover_subtree_a19642467be9
    cover_subtree_6b1d70907da0

theorem cover_subtree_ff20fb20b987 :
    adaptiveCoverCheck 7 thetaAboveCell000022003101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003101
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003101)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003101)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003101)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003101)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003101)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003101)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003101)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003101)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003101)) h))
    cover_subtree_0b78493a586a
    cover_subtree_e3814f5f5798

theorem cover_subtree_2108b1583905 :
    adaptiveCoverCheck 7 thetaAboveCell000022003102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003102)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003102)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003102)) h))
    (by
      have h : ((childHL thetaAboveCell000022003102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022003102) h)
    (by
      have h : ((childHH thetaAboveCell000022003102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022003102) h)

theorem cover_subtree_c8767f5a98fb :
    adaptiveCoverCheck 7 thetaAboveCell000022003103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003103)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003103)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003103)) h))
    (by
      have h : ((childHL thetaAboveCell000022003103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022003103) h)
    (by
      have h : ((childHH thetaAboveCell000022003103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022003103) h)

theorem cover_subtree_2ae0e1bf4a6f :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002200)))
    cover_subtree_2d90eed026dd
    cover_subtree_ff20fb20b987
    cover_subtree_2108b1583905
    cover_subtree_c8767f5a98fb

theorem cover_subtree_4c6415abff0a :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022003110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022003110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031102020
        (by
          have h : ((childLL thetaAboveCell0000220031102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031102020) h)
        (by
          have h : ((childLH thetaAboveCell0000220031102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031102020) h)
        (by
          have h : ((childHL thetaAboveCell0000220031102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031102020) h)
        (by
          have h : ((childHH thetaAboveCell0000220031102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031102020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220031102021
        (by
          have h : ((childLL thetaAboveCell0000220031102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220031102021) h)
        (by
          have h : ((childLH thetaAboveCell0000220031102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220031102021) h)
        (by
          have h : ((childHL thetaAboveCell0000220031102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220031102021) h)
        (by
          have h : ((childHH thetaAboveCell0000220031102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220031102021) h))
    (by
      have h : (thetaAboveCell0000220031102022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102022 h)
    (by
      have h : (thetaAboveCell0000220031102023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102023 h)

theorem cover_subtree_2eee4b5c26e8 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022003110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022003110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102000 h)
        (by
          have h : (thetaAboveCell0000220031102001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102001 h)
        (by
          have h : (thetaAboveCell0000220031102002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102002 h)
        (by
          have h : (thetaAboveCell0000220031102003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102010 h)
        (by
          have h : (thetaAboveCell0000220031102011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102011 h)
        (by
          have h : (thetaAboveCell0000220031102012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102012 h)
        (by
          have h : (thetaAboveCell0000220031102013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102013 h))
    cover_subtree_4c6415abff0a
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102030 h)
        (by
          have h : (thetaAboveCell0000220031102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102031 h)
        (by
          have h : (thetaAboveCell0000220031102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102032 h)
        (by
          have h : (thetaAboveCell0000220031102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102033 h))

theorem cover_subtree_a1a430be962f :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022003110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022003110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102100 h)
        (by
          have h : (thetaAboveCell0000220031102101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102101 h)
        (by
          have h : (thetaAboveCell0000220031102102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102102 h)
        (by
          have h : (thetaAboveCell0000220031102103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102110 h)
        (by
          have h : (thetaAboveCell0000220031102111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102111 h)
        (by
          have h : (thetaAboveCell0000220031102112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102112 h)
        (by
          have h : (thetaAboveCell0000220031102113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102120 h)
        (by
          have h : (thetaAboveCell0000220031102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102121 h)
        (by
          have h : (thetaAboveCell0000220031102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102122 h)
        (by
          have h : (thetaAboveCell0000220031102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102130 h)
        (by
          have h : (thetaAboveCell0000220031102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102131 h)
        (by
          have h : (thetaAboveCell0000220031102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102132 h)
        (by
          have h : (thetaAboveCell0000220031102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102133 h))

theorem cover_subtree_175aa4a9f2f2 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022003110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022003110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102200 h)
        (by
          have h : (thetaAboveCell0000220031102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102201 h)
        (by
          have h : (thetaAboveCell0000220031102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102202 h)
        (by
          have h : (thetaAboveCell0000220031102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102210 h)
        (by
          have h : (thetaAboveCell0000220031102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102211 h)
        (by
          have h : (thetaAboveCell0000220031102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102212 h)
        (by
          have h : (thetaAboveCell0000220031102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022003110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022003110))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022003110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022003110))) h)

theorem cover_subtree_b6a561db1a8e :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022003110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022003110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102300 h)
        (by
          have h : (thetaAboveCell0000220031102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102301 h)
        (by
          have h : (thetaAboveCell0000220031102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102302 h)
        (by
          have h : (thetaAboveCell0000220031102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102310 h)
        (by
          have h : (thetaAboveCell0000220031102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102311 h)
        (by
          have h : (thetaAboveCell0000220031102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102312 h)
        (by
          have h : (thetaAboveCell0000220031102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031102313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022003110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022003110))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022003110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022003110))) h)

theorem cover_subtree_e6198bf2e2be :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022003110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022003110)
    cover_subtree_2eee4b5c26e8
    cover_subtree_a1a430be962f
    cover_subtree_175aa4a9f2f2
    cover_subtree_b6a561db1a8e

theorem cover_subtree_03c6f1190393 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022003110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022003110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103000 h)
        (by
          have h : (thetaAboveCell0000220031103001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103001 h)
        (by
          have h : (thetaAboveCell0000220031103002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103002 h)
        (by
          have h : (thetaAboveCell0000220031103003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103010 h)
        (by
          have h : (thetaAboveCell0000220031103011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103011 h)
        (by
          have h : (thetaAboveCell0000220031103012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103012 h)
        (by
          have h : (thetaAboveCell0000220031103013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103020 h)
        (by
          have h : (thetaAboveCell0000220031103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103021 h)
        (by
          have h : (thetaAboveCell0000220031103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103022 h)
        (by
          have h : (thetaAboveCell0000220031103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103030 h)
        (by
          have h : (thetaAboveCell0000220031103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103031 h)
        (by
          have h : (thetaAboveCell0000220031103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103032 h)
        (by
          have h : (thetaAboveCell0000220031103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103033 h))

theorem cover_subtree_40c139979b71 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022003110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022003110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103100 h)
        (by
          have h : (thetaAboveCell0000220031103101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103101 h)
        (by
          have h : (thetaAboveCell0000220031103102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103102 h)
        (by
          have h : (thetaAboveCell0000220031103103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103110 h)
        (by
          have h : (thetaAboveCell0000220031103111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103111 h)
        (by
          have h : (thetaAboveCell0000220031103112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103112 h)
        (by
          have h : (thetaAboveCell0000220031103113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103120 h)
        (by
          have h : (thetaAboveCell0000220031103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103121 h)
        (by
          have h : (thetaAboveCell0000220031103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103122 h)
        (by
          have h : (thetaAboveCell0000220031103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103130 h)
        (by
          have h : (thetaAboveCell0000220031103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103131 h)
        (by
          have h : (thetaAboveCell0000220031103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103132 h)
        (by
          have h : (thetaAboveCell0000220031103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103133 h))

theorem cover_subtree_aa0d2321f3c9 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022003110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022003110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103200 h)
        (by
          have h : (thetaAboveCell0000220031103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103201 h)
        (by
          have h : (thetaAboveCell0000220031103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103202 h)
        (by
          have h : (thetaAboveCell0000220031103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103210 h)
        (by
          have h : (thetaAboveCell0000220031103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103211 h)
        (by
          have h : (thetaAboveCell0000220031103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103212 h)
        (by
          have h : (thetaAboveCell0000220031103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022003110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022003110))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022003110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022003110))) h)

theorem cover_subtree_fea12d0bbf6a :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022003110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022003110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103300 h)
        (by
          have h : (thetaAboveCell0000220031103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103301 h)
        (by
          have h : (thetaAboveCell0000220031103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103302 h)
        (by
          have h : (thetaAboveCell0000220031103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022003110)))
        (by
          have h : (thetaAboveCell0000220031103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103310 h)
        (by
          have h : (thetaAboveCell0000220031103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103311 h)
        (by
          have h : (thetaAboveCell0000220031103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103312 h)
        (by
          have h : (thetaAboveCell0000220031103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031103313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022003110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022003110))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022003110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022003110))) h)

theorem cover_subtree_aa69ae74ebd2 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022003110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022003110)
    cover_subtree_03c6f1190393
    cover_subtree_40c139979b71
    cover_subtree_aa0d2321f3c9
    cover_subtree_fea12d0bbf6a

theorem cover_subtree_2ac73ef77180 :
    adaptiveCoverCheck 7 thetaAboveCell000022003110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003110
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003110)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003110)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003110)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003110)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003110)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003110)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003110)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003110)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003110)) h))
    cover_subtree_e6198bf2e2be
    cover_subtree_aa69ae74ebd2

theorem cover_subtree_b28aebcb8c2e :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022003111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022003111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112000 h)
        (by
          have h : (thetaAboveCell0000220031112001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112001 h)
        (by
          have h : (thetaAboveCell0000220031112002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112002 h)
        (by
          have h : (thetaAboveCell0000220031112003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112010 h)
        (by
          have h : (thetaAboveCell0000220031112011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112011 h)
        (by
          have h : (thetaAboveCell0000220031112012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112012 h)
        (by
          have h : (thetaAboveCell0000220031112013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112020 h)
        (by
          have h : (thetaAboveCell0000220031112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112021 h)
        (by
          have h : (thetaAboveCell0000220031112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112022 h)
        (by
          have h : (thetaAboveCell0000220031112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112030 h)
        (by
          have h : (thetaAboveCell0000220031112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112031 h)
        (by
          have h : (thetaAboveCell0000220031112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112032 h)
        (by
          have h : (thetaAboveCell0000220031112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112033 h))

theorem cover_subtree_d16c7f3cc99a :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022003111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022003111))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022003111))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022003111))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112120 h)
        (by
          have h : (thetaAboveCell0000220031112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112121 h)
        (by
          have h : (thetaAboveCell0000220031112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112122 h)
        (by
          have h : (thetaAboveCell0000220031112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112130 h)
        (by
          have h : (thetaAboveCell0000220031112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112131 h)
        (by
          have h : (thetaAboveCell0000220031112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112132 h)
        (by
          have h : (thetaAboveCell0000220031112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112133 h))

theorem cover_subtree_b18c7ceea6b5 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022003111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022003111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112200 h)
        (by
          have h : (thetaAboveCell0000220031112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112201 h)
        (by
          have h : (thetaAboveCell0000220031112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112202 h)
        (by
          have h : (thetaAboveCell0000220031112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112210 h)
        (by
          have h : (thetaAboveCell0000220031112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112211 h)
        (by
          have h : (thetaAboveCell0000220031112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112212 h)
        (by
          have h : (thetaAboveCell0000220031112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022003111))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022003111))) h)

theorem cover_subtree_acda22cf7e9d :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022003111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022003111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112300 h)
        (by
          have h : (thetaAboveCell0000220031112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112301 h)
        (by
          have h : (thetaAboveCell0000220031112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112302 h)
        (by
          have h : (thetaAboveCell0000220031112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112310 h)
        (by
          have h : (thetaAboveCell0000220031112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112311 h)
        (by
          have h : (thetaAboveCell0000220031112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112312 h)
        (by
          have h : (thetaAboveCell0000220031112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031112313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022003111))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022003111))) h)

theorem cover_subtree_e026b8ce03c7 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022003111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022003111)
    cover_subtree_b28aebcb8c2e
    cover_subtree_d16c7f3cc99a
    cover_subtree_b18c7ceea6b5
    cover_subtree_acda22cf7e9d

theorem cover_subtree_f521b363acbf :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022003111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022003111))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022003111))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022003111))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113020 h)
        (by
          have h : (thetaAboveCell0000220031113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113021 h)
        (by
          have h : (thetaAboveCell0000220031113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113022 h)
        (by
          have h : (thetaAboveCell0000220031113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113030 h)
        (by
          have h : (thetaAboveCell0000220031113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113031 h)
        (by
          have h : (thetaAboveCell0000220031113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113032 h)
        (by
          have h : (thetaAboveCell0000220031113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113033 h))

theorem cover_subtree_524c47da8fe4 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022003111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022003111))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022003111))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022003111))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113120 h)
        (by
          have h : (thetaAboveCell0000220031113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113121 h)
        (by
          have h : (thetaAboveCell0000220031113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113122 h)
        (by
          have h : (thetaAboveCell0000220031113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113130 h)
        (by
          have h : (thetaAboveCell0000220031113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113131 h)
        (by
          have h : (thetaAboveCell0000220031113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113132 h)
        (by
          have h : (thetaAboveCell0000220031113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113133 h))

theorem cover_subtree_43c4b871b5bc :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022003111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022003111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113200 h)
        (by
          have h : (thetaAboveCell0000220031113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113201 h)
        (by
          have h : (thetaAboveCell0000220031113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113202 h)
        (by
          have h : (thetaAboveCell0000220031113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113210 h)
        (by
          have h : (thetaAboveCell0000220031113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113211 h)
        (by
          have h : (thetaAboveCell0000220031113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113212 h)
        (by
          have h : (thetaAboveCell0000220031113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022003111))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022003111))) h)

theorem cover_subtree_2318bf66cd31 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022003111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022003111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113300 h)
        (by
          have h : (thetaAboveCell0000220031113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113301 h)
        (by
          have h : (thetaAboveCell0000220031113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113302 h)
        (by
          have h : (thetaAboveCell0000220031113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022003111)))
        (by
          have h : (thetaAboveCell0000220031113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113310 h)
        (by
          have h : (thetaAboveCell0000220031113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113311 h)
        (by
          have h : (thetaAboveCell0000220031113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113312 h)
        (by
          have h : (thetaAboveCell0000220031113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220031113313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022003111))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022003111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022003111))) h)

theorem cover_subtree_db44c7b5c525 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022003111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022003111)
    cover_subtree_f521b363acbf
    cover_subtree_524c47da8fe4
    cover_subtree_43c4b871b5bc
    cover_subtree_2318bf66cd31

theorem cover_subtree_65fd7134399d :
    adaptiveCoverCheck 7 thetaAboveCell000022003111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003111
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003111)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003111)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003111)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003111)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003111)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003111)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003111)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003111)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003111)) h))
    cover_subtree_e026b8ce03c7
    cover_subtree_db44c7b5c525

theorem cover_subtree_0003bc3e2951 :
    adaptiveCoverCheck 7 thetaAboveCell000022003112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003112)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003112)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003112)) h))
    (by
      have h : ((childHL thetaAboveCell000022003112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022003112) h)
    (by
      have h : ((childHH thetaAboveCell000022003112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022003112) h)

theorem cover_subtree_3bc7bdc69c3a :
    adaptiveCoverCheck 7 thetaAboveCell000022003113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022003113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022003113)
        (by
          have h : ((childLL (childLL thetaAboveCell000022003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022003113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022003113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022003113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022003113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022003113)
        (by
          have h : ((childLL (childLH thetaAboveCell000022003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022003113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022003113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022003113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022003113)) h))
    (by
      have h : ((childHL thetaAboveCell000022003113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022003113) h)
    (by
      have h : ((childHH thetaAboveCell000022003113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022003113) h)

theorem cover_subtree_63491c075e54 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002200)))
    cover_subtree_2ac73ef77180
    cover_subtree_65fd7134399d
    cover_subtree_0003bc3e2951
    cover_subtree_3bc7bdc69c3a

theorem e24KC2ThetaAboveLeaf0000220031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002200))
    cover_subtree_2ae0e1bf4a6f
    cover_subtree_63491c075e54
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00002200)))
        (by
          have h : (thetaAboveCell000022003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003120 h)
        (by
          have h : (thetaAboveCell000022003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003121 h)
        (by
          have h : (thetaAboveCell000022003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003122 h)
        (by
          have h : (thetaAboveCell000022003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00002200)))
        (by
          have h : (thetaAboveCell000022003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003130 h)
        (by
          have h : (thetaAboveCell000022003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003131 h)
        (by
          have h : (thetaAboveCell000022003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003132 h)
        (by
          have h : (thetaAboveCell000022003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022003133 h))
theorem e24KC2ThetaAboveLeaf0000220032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002200))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002200))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002200))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002200))) h)
theorem e24KC2ThetaAboveLeaf0000220033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002200))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002200))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002200))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002200))) h)
theorem e24KC2ThetaAboveLeaf0000220102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00002201))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00002201))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00002201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022010220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022010220 h)
        (by
          have h : (thetaAboveCell000022010221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022010221 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022010222
            (by
              have h : ((childLL thetaAboveCell000022010222)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022010222) h)
            (by
              have h : ((childLH thetaAboveCell000022010222)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022010222) h)
            (by
              have h : ((childHL thetaAboveCell000022010222)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022010222) h)
            (by
              have h : ((childHH thetaAboveCell000022010222)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022010222) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022010223
            (by
              have h : ((childLL thetaAboveCell000022010223)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022010223) h)
            (by
              have h : ((childLH thetaAboveCell000022010223)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022010223) h)
            (by
              have h : ((childHL thetaAboveCell000022010223)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022010223) h)
            (by
              have h : ((childHH thetaAboveCell000022010223)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022010223) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022010230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022010230 h)
        (by
          have h : (thetaAboveCell000022010231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022010231 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022010232
            (by
              have h : ((childLL thetaAboveCell000022010232)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022010232) h)
            (by
              have h : ((childLH thetaAboveCell000022010232)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022010232) h)
            (by
              have h : ((childHL thetaAboveCell000022010232)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022010232) h)
            (by
              have h : ((childHH thetaAboveCell000022010232)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022010232) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022010233
            (by
              have h : ((childLL thetaAboveCell000022010233)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022010233) h)
            (by
              have h : ((childLH thetaAboveCell000022010233)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022010233) h)
            (by
              have h : ((childHL thetaAboveCell000022010233)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022010233) h)
            (by
              have h : ((childHH thetaAboveCell000022010233)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022010233) h)))
theorem e24KC2ThetaAboveLeaf0000220103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00002201))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00002201))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00002201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022010320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022010320 h)
        (by
          have h : (thetaAboveCell000022010321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022010321 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022010322
            (by
              have h : ((childLL thetaAboveCell000022010322)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022010322) h)
            (by
              have h : ((childLH thetaAboveCell000022010322)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022010322) h)
            (by
              have h : ((childHL thetaAboveCell000022010322)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022010322) h)
            (by
              have h : ((childHH thetaAboveCell000022010322)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022010322) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022010323
            (by
              have h : ((childLL thetaAboveCell000022010323)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022010323) h)
            (by
              have h : ((childLH thetaAboveCell000022010323)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022010323) h)
            (by
              have h : ((childHL thetaAboveCell000022010323)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022010323) h)
            (by
              have h : ((childHH thetaAboveCell000022010323)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022010323) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022010330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022010330 h)
        (by
          have h : (thetaAboveCell000022010331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022010331 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022010332
            (by
              have h : ((childLL thetaAboveCell000022010332)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022010332) h)
            (by
              have h : ((childLH thetaAboveCell000022010332)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022010332) h)
            (by
              have h : ((childHL thetaAboveCell000022010332)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022010332) h)
            (by
              have h : ((childHH thetaAboveCell000022010332)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022010332) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022010333
            (by
              have h : ((childLL thetaAboveCell000022010333)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022010333) h)
            (by
              have h : ((childLH thetaAboveCell000022010333)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022010333) h)
            (by
              have h : ((childHL thetaAboveCell000022010333)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022010333) h)
            (by
              have h : ((childHH thetaAboveCell000022010333)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022010333) h)))
theorem e24KC2ThetaAboveLeaf0000220112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00002201))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00002201))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00002201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022011220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022011220 h)
        (by
          have h : (thetaAboveCell000022011221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022011221 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022011222
            (by
              have h : ((childLL thetaAboveCell000022011222)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022011222) h)
            (by
              have h : ((childLH thetaAboveCell000022011222)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022011222) h)
            (by
              have h : ((childHL thetaAboveCell000022011222)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022011222) h)
            (by
              have h : ((childHH thetaAboveCell000022011222)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022011222) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022011223
            (by
              have h : ((childLL thetaAboveCell000022011223)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022011223) h)
            (by
              have h : ((childLH thetaAboveCell000022011223)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022011223) h)
            (by
              have h : ((childHL thetaAboveCell000022011223)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022011223) h)
            (by
              have h : ((childHH thetaAboveCell000022011223)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022011223) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLH
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022011230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022011230 h)
        (by
          have h : (thetaAboveCell000022011231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022011231 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022011232
            (by
              have h : ((childLL thetaAboveCell000022011232)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022011232) h)
            (by
              have h : ((childLH thetaAboveCell000022011232)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022011232) h)
            (by
              have h : ((childHL thetaAboveCell000022011232)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022011232) h)
            (by
              have h : ((childHH thetaAboveCell000022011232)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022011232) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022011233
            (by
              have h : ((childLL thetaAboveCell000022011233)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022011233) h)
            (by
              have h : ((childLH thetaAboveCell000022011233)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022011233) h)
            (by
              have h : ((childHL thetaAboveCell000022011233)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022011233) h)
            (by
              have h : ((childHH thetaAboveCell000022011233)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022011233) h)))
theorem e24KC2ThetaAboveLeaf0000220113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00002201))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00002201))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00002201))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLH
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022011320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022011320 h)
        (by
          have h : (thetaAboveCell000022011321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022011321 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022011322
            (by
              have h : ((childLL thetaAboveCell000022011322)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022011322) h)
            (by
              have h : ((childLH thetaAboveCell000022011322)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022011322) h)
            (by
              have h : ((childHL thetaAboveCell000022011322)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022011322) h)
            (by
              have h : ((childHH thetaAboveCell000022011322)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022011322) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022011323
            (by
              have h : ((childLL thetaAboveCell000022011323)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022011323) h)
            (by
              have h : ((childLH thetaAboveCell000022011323)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022011323) h)
            (by
              have h : ((childHL thetaAboveCell000022011323)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022011323) h)
            (by
              have h : ((childHH thetaAboveCell000022011323)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022011323) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLH
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022011330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022011330 h)
        (by
          have h : (thetaAboveCell000022011331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022011331 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022011332
            (by
              have h : ((childLL thetaAboveCell000022011332)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022011332) h)
            (by
              have h : ((childLH thetaAboveCell000022011332)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022011332) h)
            (by
              have h : ((childHL thetaAboveCell000022011332)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022011332) h)
            (by
              have h : ((childHH thetaAboveCell000022011332)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022011332) h))
        (by
          have h : (thetaAboveCell000022011333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022011333 h))
theorem cover_subtree_cb61b2523d2d :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022012000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022012000))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022012000))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022012000))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120002020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002020 h)
        (by
          have h : (thetaAboveCell0000220120002021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002021 h)
        (by
          have h : (thetaAboveCell0000220120002022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002022 h)
        (by
          have h : (thetaAboveCell0000220120002023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120002030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002030 h)
        (by
          have h : (thetaAboveCell0000220120002031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002031 h)
        (by
          have h : (thetaAboveCell0000220120002032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002032 h)
        (by
          have h : (thetaAboveCell0000220120002033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002033 h))

theorem cover_subtree_51c2832454de :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022012000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022012000))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022012000))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022012000))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120002120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002120 h)
        (by
          have h : (thetaAboveCell0000220120002121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002121 h)
        (by
          have h : (thetaAboveCell0000220120002122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002122 h)
        (by
          have h : (thetaAboveCell0000220120002123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120002130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002130 h)
        (by
          have h : (thetaAboveCell0000220120002131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002131 h)
        (by
          have h : (thetaAboveCell0000220120002132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002132 h)
        (by
          have h : (thetaAboveCell0000220120002133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002133 h))

theorem cover_subtree_1ce463e93cf8 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022012000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022012000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002200 h)
        (by
          have h : (thetaAboveCell0000220120002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002201 h)
        (by
          have h : (thetaAboveCell0000220120002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002202 h)
        (by
          have h : (thetaAboveCell0000220120002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002210 h)
        (by
          have h : (thetaAboveCell0000220120002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002211 h)
        (by
          have h : (thetaAboveCell0000220120002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002212 h)
        (by
          have h : (thetaAboveCell0000220120002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022012000))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022012000))) h)

theorem cover_subtree_106de882d2f1 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022012000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022012000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002300 h)
        (by
          have h : (thetaAboveCell0000220120002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002301 h)
        (by
          have h : (thetaAboveCell0000220120002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002302 h)
        (by
          have h : (thetaAboveCell0000220120002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002310 h)
        (by
          have h : (thetaAboveCell0000220120002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002311 h)
        (by
          have h : (thetaAboveCell0000220120002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002312 h)
        (by
          have h : (thetaAboveCell0000220120002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022012000))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022012000))) h)

theorem cover_subtree_a41df9d2526f :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022012000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022012000)
    cover_subtree_cb61b2523d2d
    cover_subtree_51c2832454de
    cover_subtree_1ce463e93cf8
    cover_subtree_106de882d2f1

theorem cover_subtree_850bf723be77 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022012000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022012000))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022012000))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022012000))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003020 h)
        (by
          have h : (thetaAboveCell0000220120003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003021 h)
        (by
          have h : (thetaAboveCell0000220120003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003022 h)
        (by
          have h : (thetaAboveCell0000220120003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003030 h)
        (by
          have h : (thetaAboveCell0000220120003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003031 h)
        (by
          have h : (thetaAboveCell0000220120003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003032 h)
        (by
          have h : (thetaAboveCell0000220120003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003033 h))

theorem cover_subtree_2b3d22a9b597 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022012000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022012000))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022012000))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022012000))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003120 h)
        (by
          have h : (thetaAboveCell0000220120003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003121 h)
        (by
          have h : (thetaAboveCell0000220120003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003122 h)
        (by
          have h : (thetaAboveCell0000220120003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003130 h)
        (by
          have h : (thetaAboveCell0000220120003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003131 h)
        (by
          have h : (thetaAboveCell0000220120003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003132 h)
        (by
          have h : (thetaAboveCell0000220120003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003133 h))

theorem cover_subtree_29b231fa0c5a :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022012000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022012000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003200 h)
        (by
          have h : (thetaAboveCell0000220120003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003201 h)
        (by
          have h : (thetaAboveCell0000220120003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003202 h)
        (by
          have h : (thetaAboveCell0000220120003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003210 h)
        (by
          have h : (thetaAboveCell0000220120003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003211 h)
        (by
          have h : (thetaAboveCell0000220120003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003212 h)
        (by
          have h : (thetaAboveCell0000220120003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022012000))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022012000))) h)

theorem cover_subtree_2f6ee77c9edb :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022012000)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022012000))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003300 h)
        (by
          have h : (thetaAboveCell0000220120003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003301 h)
        (by
          have h : (thetaAboveCell0000220120003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003302 h)
        (by
          have h : (thetaAboveCell0000220120003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022012000)))
        (by
          have h : (thetaAboveCell0000220120003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003310 h)
        (by
          have h : (thetaAboveCell0000220120003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003311 h)
        (by
          have h : (thetaAboveCell0000220120003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003312 h)
        (by
          have h : (thetaAboveCell0000220120003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022012000))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022012000)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022012000))) h)

theorem cover_subtree_aea54c77bf9f :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022012000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022012000)
    cover_subtree_850bf723be77
    cover_subtree_2b3d22a9b597
    cover_subtree_29b231fa0c5a
    cover_subtree_2f6ee77c9edb

theorem cover_subtree_b33563914493 :
    adaptiveCoverCheck 7 thetaAboveCell000022012000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012000
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012000)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012000)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012000)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012000)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012000)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012000)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012000)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012000)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012000)) h))
    cover_subtree_a41df9d2526f
    cover_subtree_aea54c77bf9f

theorem cover_subtree_40103f36b622 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022012001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022012001))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022012001))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022012001))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012020 h)
        (by
          have h : (thetaAboveCell0000220120012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012021 h)
        (by
          have h : (thetaAboveCell0000220120012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012022 h)
        (by
          have h : (thetaAboveCell0000220120012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012030 h)
        (by
          have h : (thetaAboveCell0000220120012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012031 h)
        (by
          have h : (thetaAboveCell0000220120012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012032 h)
        (by
          have h : (thetaAboveCell0000220120012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012033 h))

theorem cover_subtree_68b551c015fb :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022012001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022012001))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022012001))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022012001))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012120 h)
        (by
          have h : (thetaAboveCell0000220120012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012121 h)
        (by
          have h : (thetaAboveCell0000220120012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012122 h)
        (by
          have h : (thetaAboveCell0000220120012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012130 h)
        (by
          have h : (thetaAboveCell0000220120012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012131 h)
        (by
          have h : (thetaAboveCell0000220120012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012132 h)
        (by
          have h : (thetaAboveCell0000220120012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012133 h))

theorem cover_subtree_26644cd8d850 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022012001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022012001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012200 h)
        (by
          have h : (thetaAboveCell0000220120012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012201 h)
        (by
          have h : (thetaAboveCell0000220120012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012202 h)
        (by
          have h : (thetaAboveCell0000220120012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012210 h)
        (by
          have h : (thetaAboveCell0000220120012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012211 h)
        (by
          have h : (thetaAboveCell0000220120012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012212 h)
        (by
          have h : (thetaAboveCell0000220120012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022012001))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022012001))) h)

theorem cover_subtree_ceab235367fd :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022012001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022012001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012300 h)
        (by
          have h : (thetaAboveCell0000220120012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012301 h)
        (by
          have h : (thetaAboveCell0000220120012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012302 h)
        (by
          have h : (thetaAboveCell0000220120012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012310 h)
        (by
          have h : (thetaAboveCell0000220120012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012311 h)
        (by
          have h : (thetaAboveCell0000220120012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012312 h)
        (by
          have h : (thetaAboveCell0000220120012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022012001))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022012001))) h)

theorem cover_subtree_4fe093f5b1c6 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022012001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022012001)
    cover_subtree_40103f36b622
    cover_subtree_68b551c015fb
    cover_subtree_26644cd8d850
    cover_subtree_ceab235367fd

theorem cover_subtree_2a612fb4e5f9 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022012001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022012001))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022012001))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022012001))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013020 h)
        (by
          have h : (thetaAboveCell0000220120013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013021 h)
        (by
          have h : (thetaAboveCell0000220120013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013022 h)
        (by
          have h : (thetaAboveCell0000220120013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013030 h)
        (by
          have h : (thetaAboveCell0000220120013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013031 h)
        (by
          have h : (thetaAboveCell0000220120013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013032 h)
        (by
          have h : (thetaAboveCell0000220120013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013033 h))

theorem cover_subtree_9768153a3fc8 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022012001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022012001))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022012001))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022012001))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013120 h)
        (by
          have h : (thetaAboveCell0000220120013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013121 h)
        (by
          have h : (thetaAboveCell0000220120013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013122 h)
        (by
          have h : (thetaAboveCell0000220120013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013130 h)
        (by
          have h : (thetaAboveCell0000220120013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013131 h)
        (by
          have h : (thetaAboveCell0000220120013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013132 h)
        (by
          have h : (thetaAboveCell0000220120013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013133 h))

theorem cover_subtree_cc445576ceb2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022012001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022012001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013200 h)
        (by
          have h : (thetaAboveCell0000220120013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013201 h)
        (by
          have h : (thetaAboveCell0000220120013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013202 h)
        (by
          have h : (thetaAboveCell0000220120013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013210 h)
        (by
          have h : (thetaAboveCell0000220120013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013211 h)
        (by
          have h : (thetaAboveCell0000220120013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013212 h)
        (by
          have h : (thetaAboveCell0000220120013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022012001))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022012001))) h)

theorem cover_subtree_f5eaea7b07a1 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022012001)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022012001))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013300 h)
        (by
          have h : (thetaAboveCell0000220120013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013301 h)
        (by
          have h : (thetaAboveCell0000220120013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013302 h)
        (by
          have h : (thetaAboveCell0000220120013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022012001)))
        (by
          have h : (thetaAboveCell0000220120013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013310 h)
        (by
          have h : (thetaAboveCell0000220120013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013311 h)
        (by
          have h : (thetaAboveCell0000220120013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013312 h)
        (by
          have h : (thetaAboveCell0000220120013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120013313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022012001))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022012001)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022012001))) h)

theorem cover_subtree_4bf63b1ca0fb :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022012001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022012001)
    cover_subtree_2a612fb4e5f9
    cover_subtree_9768153a3fc8
    cover_subtree_cc445576ceb2
    cover_subtree_f5eaea7b07a1

theorem cover_subtree_6c90b6564adf :
    adaptiveCoverCheck 7 thetaAboveCell000022012001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012001
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012001)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012001)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012001)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012001)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012001)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012001)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012001)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012001)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012001)) h))
    cover_subtree_4fe093f5b1c6
    cover_subtree_4bf63b1ca0fb

theorem cover_subtree_4289605d46bf :
    adaptiveCoverCheck 7 thetaAboveCell000022012002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012002
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012002)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012002)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012002)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012002)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012002)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012002)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012002)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012002)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012002)) h))
    (by
      have h : ((childHL thetaAboveCell000022012002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022012002) h)
    (by
      have h : ((childHH thetaAboveCell000022012002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022012002) h)

theorem cover_subtree_c487c7959b39 :
    adaptiveCoverCheck 7 thetaAboveCell000022012003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012003
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012003)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012003)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012003)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012003)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012003)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012003)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012003)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012003)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012003)) h))
    (by
      have h : ((childHL thetaAboveCell000022012003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022012003) h)
    (by
      have h : ((childHH thetaAboveCell000022012003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022012003) h)

theorem cover_subtree_a0fc96b8fbeb :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002201)))
    cover_subtree_b33563914493
    cover_subtree_6c90b6564adf
    cover_subtree_4289605d46bf
    cover_subtree_c487c7959b39

theorem cover_subtree_5e121ac8879b :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022012010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022012010))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022012010))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022012010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102020 h)
        (by
          have h : (thetaAboveCell0000220120102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102021 h)
        (by
          have h : (thetaAboveCell0000220120102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102022 h)
        (by
          have h : (thetaAboveCell0000220120102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102030 h)
        (by
          have h : (thetaAboveCell0000220120102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102031 h)
        (by
          have h : (thetaAboveCell0000220120102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102032 h)
        (by
          have h : (thetaAboveCell0000220120102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102033 h))

theorem cover_subtree_85f348686687 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022012010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022012010))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022012010))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022012010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102120 h)
        (by
          have h : (thetaAboveCell0000220120102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102121 h)
        (by
          have h : (thetaAboveCell0000220120102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102122 h)
        (by
          have h : (thetaAboveCell0000220120102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102130 h)
        (by
          have h : (thetaAboveCell0000220120102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102131 h)
        (by
          have h : (thetaAboveCell0000220120102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102132 h)
        (by
          have h : (thetaAboveCell0000220120102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102133 h))

theorem cover_subtree_0b577b76b19a :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022012010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022012010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102200 h)
        (by
          have h : (thetaAboveCell0000220120102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102201 h)
        (by
          have h : (thetaAboveCell0000220120102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102202 h)
        (by
          have h : (thetaAboveCell0000220120102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102210 h)
        (by
          have h : (thetaAboveCell0000220120102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102211 h)
        (by
          have h : (thetaAboveCell0000220120102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102212 h)
        (by
          have h : (thetaAboveCell0000220120102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022012010))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022012010))) h)

theorem cover_subtree_56442d1d29fc :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022012010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022012010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102300 h)
        (by
          have h : (thetaAboveCell0000220120102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102301 h)
        (by
          have h : (thetaAboveCell0000220120102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102302 h)
        (by
          have h : (thetaAboveCell0000220120102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102310 h)
        (by
          have h : (thetaAboveCell0000220120102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102311 h)
        (by
          have h : (thetaAboveCell0000220120102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102312 h)
        (by
          have h : (thetaAboveCell0000220120102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120102313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022012010))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022012010))) h)

theorem cover_subtree_077e5d53ad41 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022012010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022012010)
    cover_subtree_5e121ac8879b
    cover_subtree_85f348686687
    cover_subtree_0b577b76b19a
    cover_subtree_56442d1d29fc

theorem cover_subtree_afc343ef6d9c :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022012010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022012010))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022012010))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022012010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103020 h)
        (by
          have h : (thetaAboveCell0000220120103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103021 h)
        (by
          have h : (thetaAboveCell0000220120103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103022 h)
        (by
          have h : (thetaAboveCell0000220120103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103030 h)
        (by
          have h : (thetaAboveCell0000220120103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103031 h)
        (by
          have h : (thetaAboveCell0000220120103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103032 h)
        (by
          have h : (thetaAboveCell0000220120103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103033 h))

theorem cover_subtree_bd1c188bd5cc :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022012010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022012010))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022012010))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022012010))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103120 h)
        (by
          have h : (thetaAboveCell0000220120103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103121 h)
        (by
          have h : (thetaAboveCell0000220120103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103122 h)
        (by
          have h : (thetaAboveCell0000220120103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103130 h)
        (by
          have h : (thetaAboveCell0000220120103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103131 h)
        (by
          have h : (thetaAboveCell0000220120103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103132 h)
        (by
          have h : (thetaAboveCell0000220120103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103133 h))

theorem cover_subtree_89214ff44665 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022012010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022012010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103200 h)
        (by
          have h : (thetaAboveCell0000220120103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103201 h)
        (by
          have h : (thetaAboveCell0000220120103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103202 h)
        (by
          have h : (thetaAboveCell0000220120103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103210 h)
        (by
          have h : (thetaAboveCell0000220120103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103211 h)
        (by
          have h : (thetaAboveCell0000220120103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103212 h)
        (by
          have h : (thetaAboveCell0000220120103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022012010))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022012010))) h)

theorem cover_subtree_287e5af130bf :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022012010)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022012010))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103300 h)
        (by
          have h : (thetaAboveCell0000220120103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103301 h)
        (by
          have h : (thetaAboveCell0000220120103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103302 h)
        (by
          have h : (thetaAboveCell0000220120103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022012010)))
        (by
          have h : (thetaAboveCell0000220120103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103310 h)
        (by
          have h : (thetaAboveCell0000220120103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103311 h)
        (by
          have h : (thetaAboveCell0000220120103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103312 h)
        (by
          have h : (thetaAboveCell0000220120103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120103313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022012010))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022012010)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022012010))) h)

theorem cover_subtree_bdb6f38b6019 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022012010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022012010)
    cover_subtree_afc343ef6d9c
    cover_subtree_bd1c188bd5cc
    cover_subtree_89214ff44665
    cover_subtree_287e5af130bf

theorem cover_subtree_d23bef969ca7 :
    adaptiveCoverCheck 7 thetaAboveCell000022012010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012010
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012010)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012010)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012010)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012010)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012010)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012010)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012010)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012010)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012010)) h))
    cover_subtree_077e5d53ad41
    cover_subtree_bdb6f38b6019

theorem cover_subtree_4667900dcf78 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022012011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022012011))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022012011))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022012011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112020 h)
        (by
          have h : (thetaAboveCell0000220120112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112021 h)
        (by
          have h : (thetaAboveCell0000220120112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112022 h)
        (by
          have h : (thetaAboveCell0000220120112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112030 h)
        (by
          have h : (thetaAboveCell0000220120112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112031 h)
        (by
          have h : (thetaAboveCell0000220120112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112032 h)
        (by
          have h : (thetaAboveCell0000220120112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112033 h))

theorem cover_subtree_d9c26d139205 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022012011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022012011))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022012011))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022012011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112120 h)
        (by
          have h : (thetaAboveCell0000220120112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112121 h)
        (by
          have h : (thetaAboveCell0000220120112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112122 h)
        (by
          have h : (thetaAboveCell0000220120112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112130 h)
        (by
          have h : (thetaAboveCell0000220120112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112131 h)
        (by
          have h : (thetaAboveCell0000220120112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112132 h)
        (by
          have h : (thetaAboveCell0000220120112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112133 h))

theorem cover_subtree_295321b3b4d6 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022012011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022012011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112200 h)
        (by
          have h : (thetaAboveCell0000220120112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112201 h)
        (by
          have h : (thetaAboveCell0000220120112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112202 h)
        (by
          have h : (thetaAboveCell0000220120112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112210 h)
        (by
          have h : (thetaAboveCell0000220120112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112211 h)
        (by
          have h : (thetaAboveCell0000220120112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112212 h)
        (by
          have h : (thetaAboveCell0000220120112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022012011))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022012011))) h)

theorem cover_subtree_9f2040bb35ca :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022012011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022012011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112300 h)
        (by
          have h : (thetaAboveCell0000220120112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112301 h)
        (by
          have h : (thetaAboveCell0000220120112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112302 h)
        (by
          have h : (thetaAboveCell0000220120112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112310 h)
        (by
          have h : (thetaAboveCell0000220120112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112311 h)
        (by
          have h : (thetaAboveCell0000220120112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112312 h)
        (by
          have h : (thetaAboveCell0000220120112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120112313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022012011))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022012011))) h)

theorem cover_subtree_738fba336a14 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022012011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022012011)
    cover_subtree_4667900dcf78
    cover_subtree_d9c26d139205
    cover_subtree_295321b3b4d6
    cover_subtree_9f2040bb35ca

theorem cover_subtree_4ddaba414c0c :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022012011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022012011))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022012011))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022012011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113020 h)
        (by
          have h : (thetaAboveCell0000220120113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113021 h)
        (by
          have h : (thetaAboveCell0000220120113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113022 h)
        (by
          have h : (thetaAboveCell0000220120113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113030 h)
        (by
          have h : (thetaAboveCell0000220120113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113031 h)
        (by
          have h : (thetaAboveCell0000220120113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113032 h)
        (by
          have h : (thetaAboveCell0000220120113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113033 h))

theorem cover_subtree_ecd6fc119970 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022012011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022012011))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022012011))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022012011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022012011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113120 h)
        (by
          have h : (thetaAboveCell0000220120113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113121 h)
        (by
          have h : (thetaAboveCell0000220120113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113122 h)
        (by
          have h : (thetaAboveCell0000220120113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113130 h)
        (by
          have h : (thetaAboveCell0000220120113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113131 h)
        (by
          have h : (thetaAboveCell0000220120113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113132 h)
        (by
          have h : (thetaAboveCell0000220120113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113133 h))

theorem cover_subtree_9104ec057e37 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022012011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022012011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113200 h)
        (by
          have h : (thetaAboveCell0000220120113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113201 h)
        (by
          have h : (thetaAboveCell0000220120113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113202 h)
        (by
          have h : (thetaAboveCell0000220120113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113210 h)
        (by
          have h : (thetaAboveCell0000220120113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113211 h)
        (by
          have h : (thetaAboveCell0000220120113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113212 h)
        (by
          have h : (thetaAboveCell0000220120113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHL (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113220 h)
        (by
          have h : (thetaAboveCell0000220120113221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113221 h)
        (by
          have h : (thetaAboveCell0000220120113222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113222 h)
        (by
          have h : (thetaAboveCell0000220120113223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113230 h)
        (by
          have h : (thetaAboveCell0000220120113231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113231 h)
        (by
          have h : (thetaAboveCell0000220120113232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113232 h)
        (by
          have h : (thetaAboveCell0000220120113233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113233 h))

theorem cover_subtree_019584cb80e9 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022012011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022012011))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113300 h)
        (by
          have h : (thetaAboveCell0000220120113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113301 h)
        (by
          have h : (thetaAboveCell0000220120113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113302 h)
        (by
          have h : (thetaAboveCell0000220120113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113310 h)
        (by
          have h : (thetaAboveCell0000220120113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113311 h)
        (by
          have h : (thetaAboveCell0000220120113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113312 h)
        (by
          have h : (thetaAboveCell0000220120113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113320 h)
        (by
          have h : (thetaAboveCell0000220120113321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113321 h)
        (by
          have h : (thetaAboveCell0000220120113322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113322 h)
        (by
          have h : (thetaAboveCell0000220120113323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH (childHH
        thetaAboveCell000022012011)))
        (by
          have h : (thetaAboveCell0000220120113330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113330 h)
        (by
          have h : (thetaAboveCell0000220120113331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113331 h)
        (by
          have h : (thetaAboveCell0000220120113332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113332 h)
        (by
          have h : (thetaAboveCell0000220120113333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220120113333 h))

theorem cover_subtree_a099f2429294 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022012011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022012011)
    cover_subtree_4ddaba414c0c
    cover_subtree_ecd6fc119970
    cover_subtree_9104ec057e37
    cover_subtree_019584cb80e9

theorem cover_subtree_3ff73ea428ff :
    adaptiveCoverCheck 7 thetaAboveCell000022012011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012011
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012011)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012011)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012011)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012011)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012011)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012011)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012011)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012011)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012011)) h))
    cover_subtree_738fba336a14
    cover_subtree_a099f2429294

theorem cover_subtree_9d5ad8202394 :
    adaptiveCoverCheck 7 thetaAboveCell000022012012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012012
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012012)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012012)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012012)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012012)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012012)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012012)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012012)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012012)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012012)) h))
    (by
      have h : ((childHL thetaAboveCell000022012012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022012012) h)
    (by
      have h : ((childHH thetaAboveCell000022012012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022012012) h)

theorem cover_subtree_32e4797e8235 :
    adaptiveCoverCheck 7 thetaAboveCell000022012013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022012013
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022012013)
        (by
          have h : ((childLL (childLL thetaAboveCell000022012013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022012013)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022012013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022012013)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022012013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022012013)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022012013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022012013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022012013)
        (by
          have h : ((childLL (childLH thetaAboveCell000022012013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022012013)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022012013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022012013)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022012013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022012013)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022012013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022012013)) h))
    (by
      have h : ((childHL thetaAboveCell000022012013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022012013) h)
    (by
      have h : ((childHH thetaAboveCell000022012013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022012013) h)

theorem cover_subtree_86e078def774 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00002201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00002201)))
    cover_subtree_d23bef969ca7
    cover_subtree_3ff73ea428ff
    cover_subtree_9d5ad8202394
    cover_subtree_32e4797e8235

theorem e24KC2ThetaAboveLeaf0000220120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00002201))
    cover_subtree_a0fc96b8fbeb
    cover_subtree_86e078def774
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012020 h)
        (by
          have h : (thetaAboveCell000022012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012021 h)
        (by
          have h : (thetaAboveCell000022012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012022 h)
        (by
          have h : (thetaAboveCell000022012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012030 h)
        (by
          have h : (thetaAboveCell000022012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012031 h)
        (by
          have h : (thetaAboveCell000022012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012032 h)
        (by
          have h : (thetaAboveCell000022012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022012033 h))

end PartE
end GerverSofa

end

end

end

end

end

end
