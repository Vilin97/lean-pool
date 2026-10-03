/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle018
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle019
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle020
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch034`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells84b6dd5403

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `1111331130110020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110020 : AngleCell :=
  childLL (childHL (childLL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110021 : AngleCell :=
  childLH (childHL (childLL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110022 : AngleCell :=
  childHL (childHL (childLL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110023 : AngleCell :=
  childHH (childHL (childLL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110030 : AngleCell :=
  childLL (childHH (childLL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110031 : AngleCell :=
  childLH (childHH (childLL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110032 : AngleCell :=
  childHL (childHH (childLL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110033 : AngleCell :=
  childHH (childHH (childLL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110120 : AngleCell :=
  childLL (childHL (childLH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110121 : AngleCell :=
  childLH (childHL (childLH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110122 : AngleCell :=
  childHL (childHL (childLH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110123 : AngleCell :=
  childHH (childHL (childLH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110130 : AngleCell :=
  childLL (childHH (childLH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110131 : AngleCell :=
  childLH (childHH (childLH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110132 : AngleCell :=
  childHL (childHH (childLH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110133 : AngleCell :=
  childHH (childHH (childLH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130110333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130110333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell111133113011)))

/-- Subcell `1111331130111020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111020 : AngleCell :=
  childLL (childHL (childLL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111021 : AngleCell :=
  childLH (childHL (childLL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111022 : AngleCell :=
  childHL (childHL (childLL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111023 : AngleCell :=
  childHH (childHL (childLL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111030 : AngleCell :=
  childLL (childHH (childLL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111031 : AngleCell :=
  childLH (childHH (childLL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111032 : AngleCell :=
  childHL (childHH (childLL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111033 : AngleCell :=
  childHH (childHH (childLL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111120 : AngleCell :=
  childLL (childHL (childLH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111121 : AngleCell :=
  childLH (childHL (childLH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111122 : AngleCell :=
  childHL (childHL (childLH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111123 : AngleCell :=
  childHH (childHL (childLH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111130 : AngleCell :=
  childLL (childHH (childLH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111131 : AngleCell :=
  childLH (childHH (childLH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111132 : AngleCell :=
  childHL (childHH (childLH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111133 : AngleCell :=
  childHH (childHH (childLH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell111133113011)))

/-- Subcell `1111331130111333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331130111333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell111133113011)))

end GerverSofa.PartE.CertificateCells84b6dd5403

namespace GerverSofa.PartE.CertificateCellsa837c94d6b

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsa837c94d6b

namespace GerverSofa.PartE.CertificateCellsad9f83220e

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCellsad9f83220e

namespace GerverSofa.PartE.CertificateCells9fb4000a9c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells9fb4000a9c

namespace GerverSofa.PartE.CertificateCells39e4b63459

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells39e4b63459

namespace GerverSofa.PartE.CertificateCells1f04a5458e

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022002100)))

end GerverSofa.PartE.CertificateCells1f04a5458e

namespace GerverSofa.PartE.CertificateCells6fd31b8688

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells6fd31b8688

namespace GerverSofa.PartE.CertificateCells228f0f8fd4

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022002111)))

/-- Subcell `0000220021113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022002111)))

end GerverSofa.PartE.CertificateCells228f0f8fd4

namespace GerverSofa.PartE.CertificateCells0a19d30544

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells0a19d30544

namespace GerverSofa.PartE.CertificateCells2ee5d31193

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells2ee5d31193

namespace GerverSofa.PartE.CertificateCells41213b9d19

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells41213b9d19

namespace GerverSofa.PartE.CertificateCellsb64c3c15bb

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsb64c3c15bb

namespace GerverSofa.PartE.CertificateCells32e697bee5

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131001020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001020 : AngleCell :=
  childLL (childHL (childLL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001021 : AngleCell :=
  childLH (childHL (childLL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001022 : AngleCell :=
  childHL (childHL (childLL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001023 : AngleCell :=
  childHH (childHL (childLL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001030 : AngleCell :=
  childLL (childHH (childLL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001031 : AngleCell :=
  childLH (childHH (childLL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001032 : AngleCell :=
  childHL (childHH (childLL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001033 : AngleCell :=
  childHH (childHH (childLL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell111133113100)))

/-- Subcell `1111331131001333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131001333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell111133113100)))

end GerverSofa.PartE.CertificateCells32e697bee5

namespace GerverSofa.PartE.CertificateCells64ee0fdc2a

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131002010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaBelowCell111133113100)))

/-- Subcell `1111331131002113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaBelowCell111133113100)))

end GerverSofa.PartE.CertificateCells64ee0fdc2a

namespace GerverSofa.PartE.CertificateCells30e97e201e

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022002100)))

end GerverSofa.PartE.CertificateCells30e97e201e

namespace GerverSofa.PartE.CertificateCellsd48981846f

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCellsd48981846f

namespace GerverSofa.PartE.CertificateCells2454b18c1c

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells2454b18c1c

namespace GerverSofa.PartE.CertificateCellsd87c25aa46

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCellsd87c25aa46

namespace GerverSofa.PartE.CertificateCells90183e831a

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131003000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell111133113100)))

/-- Subcell `1111331131003113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell111133113100)))

end GerverSofa.PartE.CertificateCells90183e831a

namespace GerverSofa.PartE.CertificateCells47753ffbe9

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells47753ffbe9

namespace GerverSofa.PartE.CertificateCellse21bcf4574

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellse21bcf4574

namespace GerverSofa.PartE.CertificateCellsda9a873863

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsda9a873863

namespace GerverSofa.PartE.CertificateCells7d865d7559

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131113000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell111133113111)))

/-- Subcell `1111331131113033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell111133113111)))

end GerverSofa.PartE.CertificateCells7d865d7559

namespace GerverSofa.PartE.CertificateCellsca42d19ac6

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCellsca42d19ac6

namespace GerverSofa.PartE.CertificateCells257a1a1faa

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131010200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell111133113101)))

/-- Subcell `1111331131010333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131010333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell111133113101)))

end GerverSofa.PartE.CertificateCells257a1a1faa

namespace GerverSofa.PartE.CertificateCellsb187906d24

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022002101)))

/-- Subcell `0000220021012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022002101)))

end GerverSofa.PartE.CertificateCellsb187906d24

namespace GerverSofa.PartE.CertificateCellseb98bd469c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellseb98bd469c

namespace GerverSofa.PartE.CertificateCells0fb8590a1f

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells0fb8590a1f

namespace GerverSofa.PartE.CertificateCells21614274e2

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `111133113131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `111133113132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `111133113133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells21614274e2

namespace GerverSofa.PartE.CertificateCells075667848d

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022002100)))

/-- Subcell `0000220021002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022002100)))

end GerverSofa.PartE.CertificateCells075667848d

namespace GerverSofa.PartE.CertificateCells135b119fc2

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells135b119fc2

namespace GerverSofa.PartE.CertificateCellse53a016898

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellse53a016898

namespace GerverSofa.PartE.CertificateCells8b72842cc0

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

end GerverSofa.PartE.CertificateCells8b72842cc0

namespace GerverSofa.PartE.CertificateCells3d04a04d91

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `111133113031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `111133113032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `111133113033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells3d04a04d91

namespace GerverSofa.PartE.CertificateCells665e67ba22

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131013010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell111133113101)))

/-- Subcell `1111331131013113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell111133113101)))

end GerverSofa.PartE.CertificateCells665e67ba22

namespace GerverSofa.PartE.CertificateCellsa275032fe9

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCellsa275032fe9

namespace GerverSofa.PartE.CertificateCells09124dcbf9

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCells09124dcbf9

namespace GerverSofa.PartE.CertificateCellse133bf0420

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022002110)))

/-- Subcell `0000220021102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022002110)))

end GerverSofa.PartE.CertificateCellse133bf0420

namespace GerverSofa.PartE.CertificateCellsf1833757d0

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsf1833757d0

namespace GerverSofa.PartE.CertificateCells21f94a2daf

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

end GerverSofa.PartE.CertificateCells21f94a2daf

namespace GerverSofa.PartE.CertificateCellsbb4f00460c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

end GerverSofa.PartE.CertificateCellsbb4f00460c

namespace GerverSofa.PartE.CertificateCells232e7e9a76

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `111133113021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `111133113022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell11113311)))

/-- Subcell `111133113023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells232e7e9a76

namespace GerverSofa.PartE.CertificateCellse657ecadb5

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCellse657ecadb5

namespace GerverSofa.PartE.CertificateCells78b824f474

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131110220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110200 : AngleCell :=
  childLL (childLL (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110201 : AngleCell :=
  childLH (childLL (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110202 : AngleCell :=
  childHL (childLL (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110203 : AngleCell :=
  childHH (childLL (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110210 : AngleCell :=
  childLL (childLH (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110211 : AngleCell :=
  childLH (childLH (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110212 : AngleCell :=
  childHL (childLH (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110213 : AngleCell :=
  childHH (childLH (childHL (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110300 : AngleCell :=
  childLL (childLL (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110301 : AngleCell :=
  childLH (childLL (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110302 : AngleCell :=
  childHL (childLL (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110303 : AngleCell :=
  childHH (childLL (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110310 : AngleCell :=
  childLL (childLH (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110311 : AngleCell :=
  childLH (childLH (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110312 : AngleCell :=
  childHL (childLH (childHH (childLL thetaBelowCell111133113111)))

/-- Subcell `1111331131110313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131110313 : AngleCell :=
  childHH (childLH (childHH (childLL thetaBelowCell111133113111)))

end GerverSofa.PartE.CertificateCells78b824f474

namespace GerverSofa.PartE.CertificateCellsccc2f90403

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCellsccc2f90403

namespace GerverSofa.PartE.CertificateCellse5aa25a242

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCellse5aa25a242

namespace GerverSofa.PartE.CertificateCells0d1c7d48ff

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCells0d1c7d48ff

namespace GerverSofa.PartE.CertificateCells1d418dae20

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

end GerverSofa.PartE.CertificateCells1d418dae20

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6R4Subtree8dd4d0d86bb3ff9f`.
* `KernelOnly.PartE.E24KC6R4Subtree8e967390514267d6`.
* `KernelOnly.PartE.E24KC6R4Subtree91992483bb6a8f04`.
* `KernelOnly.PartE.E24KC6R4Subtree924080aa784e817a`.
* `KernelOnly.PartE.E24KC6R4Subtree9eb1f025174c3177`.
* `KernelOnly.PartE.E24KC6R4SubtreeA095c7ff4c6ad6b6`.
* `KernelOnly.PartE.E24KC6R4Join32513267a6450294`.
* `KernelOnly.PartE.E24KC6R4SubtreeA80f1d406f4d338d`.
* `KernelOnly.PartE.E24KC6R4SubtreeAea2c9f5ded50576`.
* `KernelOnly.PartE.E24KC6R4SubtreeB93b1c054dba72bb`.
* `KernelOnly.PartE.E24KC6R4SubtreeC309c137435a4a8a`.
* `KernelOnly.PartE.E24KC6R4Join1c93c00761c21de7`.
* `KernelOnly.PartE.E24KC6R4SubtreeC8b63043186f1b44`.
* `KernelOnly.PartE.E24KC6R4SubtreeCbd4f9934ee17393`.
* `KernelOnly.PartE.E24KC6R4SubtreeD658abc468986ad2`.
* `KernelOnly.PartE.E24KC6R4SubtreeDc47723dc66dfda8`.
* `KernelOnly.PartE.E24KC6R4SubtreeE07cf48cb1b589f9`.
* `KernelOnly.PartE.E24KC6R4JoinA1daf15b91aa7155`.
* `KernelOnly.PartE.E24KC6R4SubtreeE1aad79037162af3`.
* `KernelOnly.PartE.E24KC6R4JoinB6430364d883da5c`.
* `KernelOnly.PartE.E24KC6R4SubtreeE3bcfcc291fdb5b4`.
* `KernelOnly.PartE.E24KC6R4SubtreeE5b6fc380e82e47e`.
* `KernelOnly.PartE.E24KC6R4SubtreeE8870b13405ffc13`.
* `KernelOnly.PartE.E24KC6R4Join3b19a6737a79b00f`.
* `KernelOnly.PartE.E24KC6R4SubtreeE91aff9c114b660b`.
* `KernelOnly.PartE.E24KC6R4SubtreeEc06b97bc924fb9a`.
* `KernelOnly.PartE.E24KC6R4Join62d0e072891eacfc`.
* `KernelOnly.PartE.E24KC6R4Join45f1be0097db6fa8`.
* `KernelOnly.PartE.E24KC6R4SubtreeEd73d41bc0ae6f27`.
* `KernelOnly.PartE.E24KC6R4SubtreeEdd4c8d57c5a9ded`.
* `KernelOnly.PartE.E24KC6R4Join96d3935117f8c848`.
* `KernelOnly.PartE.E24KC6R4Join7c9f3e2241f40b54`.
* `KernelOnly.PartE.E24KC6R4Join489f93824ca49e04`.
* `KernelOnly.PartE.E24KC6R4SubtreeF553a12d6978535b`.
* `KernelOnly.PartE.E24KC6R4SubtreeF60ae8a1c3b6076a`.
* `KernelOnly.PartE.E24KC6R4Join978735cf4a10b0c4`.
* `KernelOnly.PartE.E24KC6R4JoinAf86a73e06a6d340`.
* `KernelOnly.PartE.E24KC6R4SubtreeF8d6ff3220b818df`.
* `KernelOnly.PartE.E24KC6R4JoinB118d49025de8b76`.
* `KernelOnly.PartE.E24KC6R4JoinE6a27f6b8bf66074`.
* `KernelOnly.PartE.E24KC6R4Join1480e3e518aaa8b9`.
* `KernelOnly.PartE.E24KC6R4SubtreeF9a00b60dcd28a42`.
* `KernelOnly.PartE.E24KC6R4Join68100c5f054c8ea2`.
* `KernelOnly.PartE.E24KC6R4SubtreeFfa75b98dddd4b5e`.
* `KernelOnly.PartE.E24KC6R4Join25ba04fb03bf9d4a`.
* `KernelOnly.PartE.E24KC6R4JoinB0c26eb36c2c399d`.
* `KernelOnly.PartE.E24KC6R4JoinC502233200399653`.
* `KernelOnly.PartE.E24KC6R4Join459e5b5f3815ebd2`.
-/

public section

noncomputable section

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells84b6dd5403

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells84b6dd5403

open CertificateCells84b6dd5403
theorem cover_subtree_ae17a6be47c3 :
    adaptiveCoverCheck 4 (childLL (childLL thetaBelowCell111133113011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133113011))
    (by
      have h : ((childLL (childLL (childLL thetaBelowCell111133113011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
        thetaBelowCell111133113011))) h)
    (by
      have h : ((childLH (childLL (childLL thetaBelowCell111133113011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
        thetaBelowCell111133113011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110020 h)
        (by
          have h : (thetaBelowCell1111331130110021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110021 h)
        (by
          have h : (thetaBelowCell1111331130110022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110022 h)
        (by
          have h : (thetaBelowCell1111331130110023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110030 h)
        (by
          have h : (thetaBelowCell1111331130110031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110031 h)
        (by
          have h : (thetaBelowCell1111331130110032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110032 h)
        (by
          have h : (thetaBelowCell1111331130110033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110033 h))

theorem cover_subtree_370884aab783 :
    adaptiveCoverCheck 4 (childLH (childLL thetaBelowCell111133113011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133113011))
    (by
      have h : ((childLL (childLH (childLL thetaBelowCell111133113011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
        thetaBelowCell111133113011))) h)
    (by
      have h : ((childLH (childLH (childLL thetaBelowCell111133113011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
        thetaBelowCell111133113011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110120 h)
        (by
          have h : (thetaBelowCell1111331130110121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110121 h)
        (by
          have h : (thetaBelowCell1111331130110122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110122 h)
        (by
          have h : (thetaBelowCell1111331130110123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110130 h)
        (by
          have h : (thetaBelowCell1111331130110131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110131 h)
        (by
          have h : (thetaBelowCell1111331130110132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110132 h)
        (by
          have h : (thetaBelowCell1111331130110133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110133 h))

theorem cover_subtree_73e4cb204c73 :
    adaptiveCoverCheck 4 (childHL (childLL thetaBelowCell111133113011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133113011))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110200 h)
        (by
          have h : (thetaBelowCell1111331130110201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110201 h)
        (by
          have h : (thetaBelowCell1111331130110202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110202 h)
        (by
          have h : (thetaBelowCell1111331130110203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110210 h)
        (by
          have h : (thetaBelowCell1111331130110211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110211 h)
        (by
          have h : (thetaBelowCell1111331130110212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110212 h)
        (by
          have h : (thetaBelowCell1111331130110213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110220 h)
        (by
          have h : (thetaBelowCell1111331130110221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110221 h)
        (by
          have h : (thetaBelowCell1111331130110222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110222 h)
        (by
          have h : (thetaBelowCell1111331130110223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110230 h)
        (by
          have h : (thetaBelowCell1111331130110231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110231 h)
        (by
          have h : (thetaBelowCell1111331130110232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110232 h)
        (by
          have h : (thetaBelowCell1111331130110233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110233 h))

theorem cover_subtree_c1c14ad83b45 :
    adaptiveCoverCheck 4 (childHH (childLL thetaBelowCell111133113011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133113011))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110300 h)
        (by
          have h : (thetaBelowCell1111331130110301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110301 h)
        (by
          have h : (thetaBelowCell1111331130110302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110302 h)
        (by
          have h : (thetaBelowCell1111331130110303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110310 h)
        (by
          have h : (thetaBelowCell1111331130110311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110311 h)
        (by
          have h : (thetaBelowCell1111331130110312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110312 h)
        (by
          have h : (thetaBelowCell1111331130110313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110320 h)
        (by
          have h : (thetaBelowCell1111331130110321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110321 h)
        (by
          have h : (thetaBelowCell1111331130110322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110322 h)
        (by
          have h : (thetaBelowCell1111331130110323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130110330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110330 h)
        (by
          have h : (thetaBelowCell1111331130110331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110331 h)
        (by
          have h : (thetaBelowCell1111331130110332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110332 h)
        (by
          have h : (thetaBelowCell1111331130110333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130110333 h))

theorem cover_subtree_f30e12efeb1a :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133113011) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113011)
    cover_subtree_ae17a6be47c3
    cover_subtree_370884aab783
    cover_subtree_73e4cb204c73
    cover_subtree_c1c14ad83b45

theorem cover_subtree_98d9e5389017 :
    adaptiveCoverCheck 4 (childLL (childLH thetaBelowCell111133113011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113011))
    (by
      have h : ((childLL (childLL (childLH thetaBelowCell111133113011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
        thetaBelowCell111133113011))) h)
    (by
      have h : ((childLH (childLL (childLH thetaBelowCell111133113011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
        thetaBelowCell111133113011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111020 h)
        (by
          have h : (thetaBelowCell1111331130111021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111021 h)
        (by
          have h : (thetaBelowCell1111331130111022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111022 h)
        (by
          have h : (thetaBelowCell1111331130111023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111030 h)
        (by
          have h : (thetaBelowCell1111331130111031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111031 h)
        (by
          have h : (thetaBelowCell1111331130111032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111032 h)
        (by
          have h : (thetaBelowCell1111331130111033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111033 h))

theorem cover_subtree_0bc86d85f103 :
    adaptiveCoverCheck 4 (childLH (childLH thetaBelowCell111133113011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133113011))
    (by
      have h : ((childLL (childLH (childLH thetaBelowCell111133113011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
        thetaBelowCell111133113011))) h)
    (by
      have h : ((childLH (childLH (childLH thetaBelowCell111133113011)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
        thetaBelowCell111133113011))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLH (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111120 h)
        (by
          have h : (thetaBelowCell1111331130111121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111121 h)
        (by
          have h : (thetaBelowCell1111331130111122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111122 h)
        (by
          have h : (thetaBelowCell1111331130111123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111130 h)
        (by
          have h : (thetaBelowCell1111331130111131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111131 h)
        (by
          have h : (thetaBelowCell1111331130111132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111132 h)
        (by
          have h : (thetaBelowCell1111331130111133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111133 h))

theorem cover_subtree_29f3a4c72110 :
    adaptiveCoverCheck 4 (childHL (childLH thetaBelowCell111133113011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113011))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111200 h)
        (by
          have h : (thetaBelowCell1111331130111201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111201 h)
        (by
          have h : (thetaBelowCell1111331130111202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111202 h)
        (by
          have h : (thetaBelowCell1111331130111203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111210 h)
        (by
          have h : (thetaBelowCell1111331130111211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111211 h)
        (by
          have h : (thetaBelowCell1111331130111212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111212 h)
        (by
          have h : (thetaBelowCell1111331130111213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111220 h)
        (by
          have h : (thetaBelowCell1111331130111221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111221 h)
        (by
          have h : (thetaBelowCell1111331130111222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111222 h)
        (by
          have h : (thetaBelowCell1111331130111223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111230 h)
        (by
          have h : (thetaBelowCell1111331130111231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111231 h)
        (by
          have h : (thetaBelowCell1111331130111232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111232 h)
        (by
          have h : (thetaBelowCell1111331130111233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111233 h))

theorem cover_subtree_71904a1bf379 :
    adaptiveCoverCheck 4 (childHH (childLH thetaBelowCell111133113011)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113011))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111300 h)
        (by
          have h : (thetaBelowCell1111331130111301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111301 h)
        (by
          have h : (thetaBelowCell1111331130111302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111302 h)
        (by
          have h : (thetaBelowCell1111331130111303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111310 h)
        (by
          have h : (thetaBelowCell1111331130111311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111311 h)
        (by
          have h : (thetaBelowCell1111331130111312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111312 h)
        (by
          have h : (thetaBelowCell1111331130111313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111320 h)
        (by
          have h : (thetaBelowCell1111331130111321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111321 h)
        (by
          have h : (thetaBelowCell1111331130111322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111322 h)
        (by
          have h : (thetaBelowCell1111331130111323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH
        thetaBelowCell111133113011)))
        (by
          have h : (thetaBelowCell1111331130111330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111330 h)
        (by
          have h : (thetaBelowCell1111331130111331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111331 h)
        (by
          have h : (thetaBelowCell1111331130111332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111332 h)
        (by
          have h : (thetaBelowCell1111331130111333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331130111333 h))

theorem cover_subtree_c4f09e9f0953 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113011) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113011)
    cover_subtree_98d9e5389017
    cover_subtree_0bc86d85f103
    cover_subtree_29f3a4c72110
    cover_subtree_71904a1bf379

theorem cover_subtree_f6e8aaad1d7c :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133113011) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133113011)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL thetaBelowCell111133113011))
        (by
          have h : ((childLL (childLL (childHL thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHL
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childLH (childLL (childHL thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHL
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL
            thetaBelowCell111133113011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL thetaBelowCell111133113011))
        (by
          have h : ((childLL (childLH (childHL thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHL
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childLH (childLH (childHL thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHL
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL
            thetaBelowCell111133113011))) h))
    (by
      have h : ((childHL (childHL thetaBelowCell111133113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL thetaBelowCell111133113011)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell111133113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL thetaBelowCell111133113011)) h)

theorem cover_subtree_29b6f04811a1 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133113011) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133113011)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH thetaBelowCell111133113011))
        (by
          have h : ((childLL (childLL (childHH thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHH
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childLH (childLL (childHH thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childHH
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH
            thetaBelowCell111133113011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH thetaBelowCell111133113011))
        (by
          have h : ((childLL (childLH (childHH thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childHH
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childLH (childLH (childHH thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childHH
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH
            thetaBelowCell111133113011))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell111133113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHH
            thetaBelowCell111133113011))) h))
    (by
      have h : ((childHL (childHH thetaBelowCell111133113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH thetaBelowCell111133113011)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell111133113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH thetaBelowCell111133113011)) h)

theorem e24KC2ThetaBelowLeaf111133113_c0_c1_c1 :
    adaptiveCoverCheck 6 thetaBelowCell111133113011 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113011
    cover_subtree_f30e12efeb1a
    cover_subtree_c4f09e9f0953
    cover_subtree_f6e8aaad1d7c
    cover_subtree_29b6f04811a1

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

namespace CertificateCellsa837c94d6b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa837c94d6b

open CertificateCellsa837c94d6b
theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022002100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022002100)
    (by
      have h : ((childLL (childLH thetaAboveCell000022002100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH thetaAboveCell000022002100)) h)
    (by
      have h : ((childLH (childLH thetaAboveCell000022002100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH thetaAboveCell000022002100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022002100))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022002100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022002100))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022002100))) h))

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

namespace CertificateCellsad9f83220e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsad9f83220e

open CertificateCellsad9f83220e
theorem e24KC2ThetaBelowLeaf111133113_c3 :
    adaptiveCoverCheck 8 (childHH (childHH thetaBelowCell11113311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH thetaBelowCell11113311))
    (by
      have h : ((childLL (childHH (childHH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLL (childHH (childHH
        thetaBelowCell11113311))) h)
    (by
      have h : ((childLH (childHH (childHH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childLH (childHH (childHH
        thetaBelowCell11113311))) h)
    (by
      have h : ((childHL (childHH (childHH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHL (childHH (childHH
        thetaBelowCell11113311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaBelowCell11113311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 (childHH (childHH (childHH
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

namespace CertificateCells9fb4000a9c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells9fb4000a9c

open CertificateCells9fb4000a9c
theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c0 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022002100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022002100)
    (by
      have h : ((childLL (childLL thetaAboveCell000022002100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL thetaAboveCell000022002100)) h)
    (by
      have h : ((childLH (childLL thetaAboveCell000022002100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL thetaAboveCell000022002100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022002100))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022002100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022002100))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022002100))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022002100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022002100))) h))

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

namespace CertificateCells39e4b63459

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells39e4b63459

open CertificateCells39e4b63459
theorem e24KC2ThetaAboveLeaf0000220021_c0_c3 :
    adaptiveCoverCheck 7 thetaAboveCell000022002103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022002103)
        (by
          have h : ((childLL (childLL thetaAboveCell000022002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022002103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022002103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022002103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022002103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022002103)
        (by
          have h : ((childLL (childLH thetaAboveCell000022002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022002103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022002103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022002103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022002103)) h))
    (by
      have h : ((childHL thetaAboveCell000022002103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022002103) h)
    (by
      have h : ((childHH thetaAboveCell000022002103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022002103) h)

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

namespace CertificateCells1f04a5458e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells1f04a5458e

open CertificateCells1f04a5458e
theorem cover_subtree_ac4ab9e2280b :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003102 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003102
    (by
      have h : ((childLL thetaAboveCell0000220021003102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003102) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003102) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003102)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003102)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003102)) h))

theorem cover_subtree_f32049ef12fd :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003103 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003103
    (by
      have h : ((childLL thetaAboveCell0000220021003103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003103) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003103) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003103)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003103)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003103)) h))

theorem cover_subtree_f8ee2b69a6a4 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021003100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003100 h)
    (by
      have h : (thetaAboveCell0000220021003101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003101 h)
    cover_subtree_ac4ab9e2280b
    cover_subtree_f32049ef12fd

theorem cover_subtree_81e656cd512a :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003112 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003112
    (by
      have h : ((childLL thetaAboveCell0000220021003112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003112) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003112) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003112)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003112)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003112)) h))

theorem cover_subtree_4d1806a48386 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003113 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003113
    (by
      have h : ((childLL thetaAboveCell0000220021003113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003113) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003113) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003113)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003113)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003113)) h))

theorem cover_subtree_08c961b8fea6 :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021003110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003110 h)
    (by
      have h : (thetaAboveCell0000220021003111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003111 h)
    cover_subtree_81e656cd512a
    cover_subtree_4d1806a48386

theorem cover_subtree_ac21c862ec3a :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003120 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003120
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003120)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003120)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003120)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003120)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003120)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003120)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003120)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003120)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003120)) h))

theorem cover_subtree_535d1cff404c :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003121 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003121
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003121)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003121)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003121)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003121)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003121)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003121)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003121)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003121)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003121)) h))

theorem cover_subtree_c98fab407e07 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022002100)))
    cover_subtree_ac21c862ec3a
    cover_subtree_535d1cff404c
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003122
        (by
          have h : ((childLL thetaAboveCell0000220021003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003122) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003122) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003122) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003123
        (by
          have h : ((childLL thetaAboveCell0000220021003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003123) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003123) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003123) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003123) h))

theorem cover_subtree_6d1eab6c80cc :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003130 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003130
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003130)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003130)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003130)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003130)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003130)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003130)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003130)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003130)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003130)) h))

theorem cover_subtree_d7741bcc2937 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003131 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003131
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003131)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003131)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003131)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003131)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003131)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003131)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003131)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003131)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003131)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003131)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003131)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003131)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003131)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003131)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003131)) h))
    (by
      have h : ((childHH thetaAboveCell0000220021003131)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003131) h)

theorem cover_subtree_db05fb36c692 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022002100)))
    cover_subtree_6d1eab6c80cc
    cover_subtree_d7741bcc2937
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003132
        (by
          have h : ((childLL thetaAboveCell0000220021003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003132) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003132) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003132) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003133
        (by
          have h : ((childLL thetaAboveCell0000220021003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003133) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003133) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003133) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003133) h))

theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c1 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002100))
    cover_subtree_f8ee2b69a6a4
    cover_subtree_08c961b8fea6
    cover_subtree_c98fab407e07
    cover_subtree_db05fb36c692

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6fd31b8688

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6fd31b8688

open CertificateCells6fd31b8688

theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002100) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002100)
    e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c0 e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c1
      e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c2 e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c3

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

namespace CertificateCells228f0f8fd4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells228f0f8fd4

open CertificateCells228f0f8fd4
theorem cover_subtree_d5a5e06650ce :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
    thetaAboveCell000022002111)))
    (by
      have h : (thetaAboveCell0000220021113000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113000 h)
    (by
      have h : (thetaAboveCell0000220021113001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113002
        (by
          have h : ((childLL thetaAboveCell0000220021113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113002) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113002) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113002) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113003
        (by
          have h : ((childLL thetaAboveCell0000220021113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113003) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113003) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113003) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113003) h))

theorem cover_subtree_cc0b6dcb9698 :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
    thetaAboveCell000022002111)))
    (by
      have h : (thetaAboveCell0000220021113010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113010 h)
    (by
      have h : (thetaAboveCell0000220021113011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113012
        (by
          have h : ((childLL thetaAboveCell0000220021113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113012) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113012) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113012) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113013
        (by
          have h : ((childLL thetaAboveCell0000220021113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113013) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113013) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113013) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113013) h))

theorem cover_subtree_4b6a6f343911 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022002111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113020
        (by
          have h : ((childLL thetaAboveCell0000220021113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113020) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113020) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113020) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113021
        (by
          have h : ((childLL thetaAboveCell0000220021113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113021) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113021) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113021) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113022
        (by
          have h : ((childLL thetaAboveCell0000220021113022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113022) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113022) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113022) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113023
        (by
          have h : ((childLL thetaAboveCell0000220021113023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113023) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113023) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113023) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113023) h))

theorem cover_subtree_3b5c8a093b1d :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022002111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113030
        (by
          have h : ((childLL thetaAboveCell0000220021113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113030) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113030) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113030) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113031
        (by
          have h : ((childLL thetaAboveCell0000220021113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113031) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113031) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113031) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113032
        (by
          have h : ((childLL thetaAboveCell0000220021113032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113032) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113032) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113032) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113033
        (by
          have h : ((childLL thetaAboveCell0000220021113033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113033) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113033) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113033) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113033) h))

theorem cover_subtree_536b999011e3 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002111))
    cover_subtree_d5a5e06650ce
    cover_subtree_cc0b6dcb9698
    cover_subtree_4b6a6f343911
    cover_subtree_3b5c8a093b1d

theorem cover_subtree_34d62deb6720 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHH
    thetaAboveCell000022002111)))
    (by
      have h : (thetaAboveCell0000220021113100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113100 h)
    (by
      have h : (thetaAboveCell0000220021113101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113102
        (by
          have h : ((childLL thetaAboveCell0000220021113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113102) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113102) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113102) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113103
        (by
          have h : ((childLL thetaAboveCell0000220021113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113103) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113103) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113103) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113103) h))

theorem cover_subtree_e8b5cb8c6a09 :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHH
    thetaAboveCell000022002111)))
    (by
      have h : (thetaAboveCell0000220021113110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113110 h)
    (by
      have h : (thetaAboveCell0000220021113111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113112
        (by
          have h : ((childLL thetaAboveCell0000220021113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113112) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113112) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113112) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113113
        (by
          have h : ((childLL thetaAboveCell0000220021113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113113) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113113) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113113) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113113) h))

theorem cover_subtree_ef6f45c91ec2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
    thetaAboveCell000022002111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113120
        (by
          have h : ((childLL thetaAboveCell0000220021113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113120) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113120) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113120) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113121
        (by
          have h : ((childLL thetaAboveCell0000220021113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113121) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113121) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113121) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113122
        (by
          have h : ((childLL thetaAboveCell0000220021113122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113122) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113122) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113122) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113123
        (by
          have h : ((childLL thetaAboveCell0000220021113123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113123) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113123) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113123) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113123) h))

theorem cover_subtree_a2fe78f78c5a :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
    thetaAboveCell000022002111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113130
        (by
          have h : ((childLL thetaAboveCell0000220021113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113130) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113130) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113130) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113131
        (by
          have h : ((childLL thetaAboveCell0000220021113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113131) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113131) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113131) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113132
        (by
          have h : ((childLL thetaAboveCell0000220021113132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113132) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113132) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113132) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021113133
        (by
          have h : ((childLL thetaAboveCell0000220021113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021113133) h)
        (by
          have h : ((childLH thetaAboveCell0000220021113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021113133) h)
        (by
          have h : ((childHL thetaAboveCell0000220021113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021113133) h)
        (by
          have h : ((childHH thetaAboveCell0000220021113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021113133) h))

theorem cover_subtree_42bf432f3a23 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022002111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022002111))
    cover_subtree_34d62deb6720
    cover_subtree_e8b5cb8c6a09
    cover_subtree_ef6f45c91ec2
    cover_subtree_a2fe78f78c5a

theorem cover_subtree_a6728f6d4a12 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022002111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022002111)))
        (by
          have h : (thetaAboveCell0000220021113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113200 h)
        (by
          have h : (thetaAboveCell0000220021113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113201 h)
        (by
          have h : (thetaAboveCell0000220021113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113202 h)
        (by
          have h : (thetaAboveCell0000220021113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022002111)))
        (by
          have h : (thetaAboveCell0000220021113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113210 h)
        (by
          have h : (thetaAboveCell0000220021113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113211 h)
        (by
          have h : (thetaAboveCell0000220021113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113212 h)
        (by
          have h : (thetaAboveCell0000220021113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022002111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022002111))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022002111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022002111))) h)

theorem cover_subtree_fafcbbc2f9f1 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022002111))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022002111)))
        (by
          have h : (thetaAboveCell0000220021113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113300 h)
        (by
          have h : (thetaAboveCell0000220021113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113301 h)
        (by
          have h : (thetaAboveCell0000220021113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113302 h)
        (by
          have h : (thetaAboveCell0000220021113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022002111)))
        (by
          have h : (thetaAboveCell0000220021113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113310 h)
        (by
          have h : (thetaAboveCell0000220021113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113311 h)
        (by
          have h : (thetaAboveCell0000220021113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113312 h)
        (by
          have h : (thetaAboveCell0000220021113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021113313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022002111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022002111))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022002111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022002111))) h)

theorem e24KC2ThetaAboveLeaf0000220021_c1_c1_c3 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022002111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022002111)
    cover_subtree_536b999011e3
    cover_subtree_42bf432f3a23
    cover_subtree_a6728f6d4a12
    cover_subtree_fafcbbc2f9f1

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

namespace CertificateCells0a19d30544

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0a19d30544

open CertificateCells0a19d30544
theorem e24KC2ThetaAboveLeaf0000220021_c1_c3 :
    adaptiveCoverCheck 7 thetaAboveCell000022002113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022002113)
        (by
          have h : ((childLL (childLL thetaAboveCell000022002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022002113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022002113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022002113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022002113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022002113)
        (by
          have h : ((childLL (childLH thetaAboveCell000022002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022002113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022002113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022002113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022002113)) h))
    (by
      have h : ((childHL thetaAboveCell000022002113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022002113) h)
    (by
      have h : ((childHH thetaAboveCell000022002113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022002113) h)

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

namespace CertificateCells2ee5d31193

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2ee5d31193

open CertificateCells2ee5d31193
theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c3 :
    adaptiveCoverCheck 6 thetaBelowCell111133113103 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113103
    (by
      have h : ((childLL thetaBelowCell111133113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133113103) h)
    (by
      have h : ((childLH thetaBelowCell111133113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133113103) h)
    (by
      have h : ((childHL thetaBelowCell111133113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133113103) h)
    (by
      have h : ((childHH thetaBelowCell111133113103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133113103) h)

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

namespace CertificateCells41213b9d19

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells41213b9d19

open CertificateCells41213b9d19
theorem e24KC2ThetaAboveLeaf0000220021_c1_c1_c0 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022002111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022002111)
    (by
      have h : ((childLL (childLL thetaAboveCell000022002111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL thetaAboveCell000022002111)) h)
    (by
      have h : ((childLH (childLL thetaAboveCell000022002111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL thetaAboveCell000022002111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022002111))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022002111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022002111))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022002111))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022002111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022002111))) h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb64c3c15bb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb64c3c15bb

open CertificateCellsb64c3c15bb

theorem e24KC2ThetaAboveLeaf0000220021_c1_c1 :
    adaptiveCoverCheck 7 thetaAboveCell000022002111 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002111
    e24KC2ThetaAboveLeaf0000220021_c1_c1_c0 e24KC2ThetaAboveLeaf0000220021_c1_c1_c1
      e24KC2ThetaAboveLeaf0000220021_c1_c1_c2 e24KC2ThetaAboveLeaf0000220021_c1_c1_c3

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

namespace CertificateCells32e697bee5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells32e697bee5

open CertificateCells32e697bee5
theorem cover_subtree_401efdae503c :
    adaptiveCoverCheck 4 (childLL (childLH thetaBelowCell111133113100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113100))
    (by
      have h : ((childLL (childLL (childLH thetaBelowCell111133113100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
        thetaBelowCell111133113100))) h)
    (by
      have h : ((childLH (childLL (childLH thetaBelowCell111133113100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
        thetaBelowCell111133113100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001020 h)
        (by
          have h : (thetaBelowCell1111331131001021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001021 h)
        (by
          have h : (thetaBelowCell1111331131001022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001022 h)
        (by
          have h : (thetaBelowCell1111331131001023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001030 h)
        (by
          have h : (thetaBelowCell1111331131001031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001031 h)
        (by
          have h : (thetaBelowCell1111331131001032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001032 h)
        (by
          have h : (thetaBelowCell1111331131001033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001033 h))

theorem cover_subtree_d2432b059763 :
    adaptiveCoverCheck 4 (childHL (childLH thetaBelowCell111133113100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113100))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001200 h)
        (by
          have h : (thetaBelowCell1111331131001201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001201 h)
        (by
          have h : (thetaBelowCell1111331131001202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001202 h)
        (by
          have h : (thetaBelowCell1111331131001203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001210 h)
        (by
          have h : (thetaBelowCell1111331131001211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001211 h)
        (by
          have h : (thetaBelowCell1111331131001212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001212 h)
        (by
          have h : (thetaBelowCell1111331131001213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001220 h)
        (by
          have h : (thetaBelowCell1111331131001221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001221 h)
        (by
          have h : (thetaBelowCell1111331131001222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001222 h)
        (by
          have h : (thetaBelowCell1111331131001223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001230 h)
        (by
          have h : (thetaBelowCell1111331131001231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001231 h)
        (by
          have h : (thetaBelowCell1111331131001232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001232 h)
        (by
          have h : (thetaBelowCell1111331131001233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001233 h))

theorem cover_subtree_a9ad7d61343c :
    adaptiveCoverCheck 4 (childHH (childLH thetaBelowCell111133113100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113100))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001300 h)
        (by
          have h : (thetaBelowCell1111331131001301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001301 h)
        (by
          have h : (thetaBelowCell1111331131001302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001302 h)
        (by
          have h : (thetaBelowCell1111331131001303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001310 h)
        (by
          have h : (thetaBelowCell1111331131001311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001311 h)
        (by
          have h : (thetaBelowCell1111331131001312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001312 h)
        (by
          have h : (thetaBelowCell1111331131001313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001320 h)
        (by
          have h : (thetaBelowCell1111331131001321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001321 h)
        (by
          have h : (thetaBelowCell1111331131001322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001322 h)
        (by
          have h : (thetaBelowCell1111331131001323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH
        thetaBelowCell111133113100)))
        (by
          have h : (thetaBelowCell1111331131001330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001330 h)
        (by
          have h : (thetaBelowCell1111331131001331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001331 h)
        (by
          have h : (thetaBelowCell1111331131001332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001332 h)
        (by
          have h : (thetaBelowCell1111331131001333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131001333 h))

theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c0_c1 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113100) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113100)
    cover_subtree_401efdae503c
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133113100))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133113100))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133113100))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133113100))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133113100))) h))
    cover_subtree_d2432b059763
    cover_subtree_a9ad7d61343c

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

namespace CertificateCells64ee0fdc2a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells64ee0fdc2a

open CertificateCells64ee0fdc2a
theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c0_c2 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133113100) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133113100)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL thetaBelowCell111133113100))
        (by
          have h : ((childLL (childLL (childHL thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childHL
            thetaBelowCell111133113100))) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHL
            thetaBelowCell111133113100)))
            (by
              have h : (thetaBelowCell1111331131002010).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002010 h)
            (by
              have h : (thetaBelowCell1111331131002011).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002011 h)
            (by
              have h : (thetaBelowCell1111331131002012).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002012 h)
            (by
              have h : (thetaBelowCell1111331131002013).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002013 h))
        (by
          have h : ((childHL (childLL (childHL thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHL
            thetaBelowCell111133113100))) h)
        (by
          have h : ((childHH (childLL (childHL thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHL
            thetaBelowCell111133113100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL thetaBelowCell111133113100))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHL
            thetaBelowCell111133113100)))
            (by
              have h : (thetaBelowCell1111331131002100).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002100 h)
            (by
              have h : (thetaBelowCell1111331131002101).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002101 h)
            (by
              have h : (thetaBelowCell1111331131002102).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002102 h)
            (by
              have h : (thetaBelowCell1111331131002103).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002103 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHL
            thetaBelowCell111133113100)))
            (by
              have h : (thetaBelowCell1111331131002110).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002110 h)
            (by
              have h : (thetaBelowCell1111331131002111).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002111 h)
            (by
              have h : (thetaBelowCell1111331131002112).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002112 h)
            (by
              have h : (thetaBelowCell1111331131002113).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131002113 h))
        (by
          have h : ((childHL (childLH (childHL thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHL
            thetaBelowCell111133113100))) h)
        (by
          have h : ((childHH (childLH (childHL thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHL
            thetaBelowCell111133113100))) h))
    (by
      have h : ((childHL (childHL thetaBelowCell111133113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL thetaBelowCell111133113100)) h)
    (by
      have h : ((childHH (childHL thetaBelowCell111133113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL thetaBelowCell111133113100)) h)

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

namespace CertificateCells30e97e201e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells30e97e201e

open CertificateCells30e97e201e
theorem cover_subtree_5271df7a6cfb :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002002 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002002
    (by
      have h : ((childLL thetaAboveCell0000220021002002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002002) h)
    (by
      have h : ((childLH thetaAboveCell0000220021002002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002002) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002002)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002002)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002002)) h))

theorem cover_subtree_ecb69e009e0c :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002003 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002003
    (by
      have h : ((childLL thetaAboveCell0000220021002003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002003) h)
    (by
      have h : ((childLH thetaAboveCell0000220021002003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002003) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002003)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002003)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002003)) h))

theorem cover_subtree_3d1aed828393 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021002000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002000 h)
    (by
      have h : (thetaAboveCell0000220021002001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002001 h)
    cover_subtree_5271df7a6cfb
    cover_subtree_ecb69e009e0c

theorem cover_subtree_b9bf7e1adc6d :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002012 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002012
    (by
      have h : ((childLL thetaAboveCell0000220021002012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002012) h)
    (by
      have h : ((childLH thetaAboveCell0000220021002012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002012) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002012)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002012)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002012)) h))

theorem cover_subtree_e49d7d8f5134 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002013 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002013
    (by
      have h : ((childLL thetaAboveCell0000220021002013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002013) h)
    (by
      have h : ((childLH thetaAboveCell0000220021002013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002013) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002013)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002013)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002013)) h))

theorem cover_subtree_e1d0aa057fae :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021002010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002010 h)
    (by
      have h : (thetaAboveCell0000220021002011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002011 h)
    cover_subtree_b9bf7e1adc6d
    cover_subtree_e49d7d8f5134

theorem cover_subtree_da176857c63b :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002020 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002020
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021002020)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021002020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021002020)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021002020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002020)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002020)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002020)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002020)) h))

theorem cover_subtree_6fcd4b6c5e8d :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002021 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002021
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021002021)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021002021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021002021)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021002021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002021)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002021)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002021)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002021)) h))

theorem cover_subtree_6d0fa2f909d3 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022002100)))
    cover_subtree_da176857c63b
    cover_subtree_6fcd4b6c5e8d
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002022
        (by
          have h : ((childLL thetaAboveCell0000220021002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002022) h)
        (by
          have h : ((childLH thetaAboveCell0000220021002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002022) h)
        (by
          have h : ((childHL thetaAboveCell0000220021002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021002022) h)
        (by
          have h : ((childHH thetaAboveCell0000220021002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021002022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002023
        (by
          have h : ((childLL thetaAboveCell0000220021002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002023) h)
        (by
          have h : ((childLH thetaAboveCell0000220021002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002023) h)
        (by
          have h : ((childHL thetaAboveCell0000220021002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021002023) h)
        (by
          have h : ((childHH thetaAboveCell0000220021002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021002023) h))

theorem cover_subtree_db002a1c8e4f :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002030 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002030
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021002030)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021002030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021002030)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021002030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002030)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002030)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002030)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002030)) h))

theorem cover_subtree_b3dca0ca0dcf :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002031 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002031
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021002031)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021002031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021002031)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021002031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002031)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002031)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002031)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002031)) h))

theorem cover_subtree_78fc8a461c2f :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022002100)))
    cover_subtree_db002a1c8e4f
    cover_subtree_b3dca0ca0dcf
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002032
        (by
          have h : ((childLL thetaAboveCell0000220021002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002032) h)
        (by
          have h : ((childLH thetaAboveCell0000220021002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002032) h)
        (by
          have h : ((childHL thetaAboveCell0000220021002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021002032) h)
        (by
          have h : ((childHH thetaAboveCell0000220021002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021002032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002033
        (by
          have h : ((childLL thetaAboveCell0000220021002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002033) h)
        (by
          have h : ((childLH thetaAboveCell0000220021002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002033) h)
        (by
          have h : ((childHL thetaAboveCell0000220021002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021002033) h)
        (by
          have h : ((childHH thetaAboveCell0000220021002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021002033) h))

theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c2_c0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002100))
    cover_subtree_3d1aed828393
    cover_subtree_e1d0aa057fae
    cover_subtree_6d0fa2f909d3
    cover_subtree_78fc8a461c2f

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

namespace CertificateCellsd48981846f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd48981846f

open CertificateCellsd48981846f
theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3_c3 :
    adaptiveCoverCheck 4 (childHH (childHH thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHH (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHH (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHL (childHH (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHH (childHH (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
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

namespace CertificateCells2454b18c1c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2454b18c1c

open CertificateCells2454b18c1c
theorem e24KC2ThetaBelowLeaf111133113_c0_c1_c2 :
    adaptiveCoverCheck 6 thetaBelowCell111133113012 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113012
    (by
      have h : ((childLL thetaBelowCell111133113012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL thetaBelowCell111133113012) h)
    (by
      have h : ((childLH thetaBelowCell111133113012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH thetaBelowCell111133113012) h)
    (by
      have h : ((childHL thetaBelowCell111133113012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133113012) h)
    (by
      have h : ((childHH thetaBelowCell111133113012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133113012) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd87c25aa46

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd87c25aa46

open CertificateCellsd87c25aa46

theorem e24KC2ThetaBelowLeaf111133113_c0_c1 :
    adaptiveCoverCheck 7 (childLH (childLL (childHH thetaBelowCell11113311))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLH (childLL (childHH thetaBelowCell11113311)))
    e24KC2ThetaBelowLeaf111133113_c0_c1_c0 e24KC2ThetaBelowLeaf111133113_c0_c1_c1
      e24KC2ThetaBelowLeaf111133113_c0_c1_c2 e24KC2ThetaBelowLeaf111133113_c0_c1_c3

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

namespace CertificateCells90183e831a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells90183e831a

open CertificateCells90183e831a
theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c0_c3 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133113100) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133113100)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH thetaBelowCell111133113100))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHH
            thetaBelowCell111133113100)))
            (by
              have h : (thetaBelowCell1111331131003000).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003000 h)
            (by
              have h : (thetaBelowCell1111331131003001).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003001 h)
            (by
              have h : (thetaBelowCell1111331131003002).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003002 h)
            (by
              have h : (thetaBelowCell1111331131003003).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003003 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHH
            thetaBelowCell111133113100)))
            (by
              have h : (thetaBelowCell1111331131003010).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003010 h)
            (by
              have h : (thetaBelowCell1111331131003011).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003011 h)
            (by
              have h : (thetaBelowCell1111331131003012).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003012 h)
            (by
              have h : (thetaBelowCell1111331131003013).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003013 h))
        (by
          have h : ((childHL (childLL (childHH thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH
            thetaBelowCell111133113100))) h)
        (by
          have h : ((childHH (childLL (childHH thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH
            thetaBelowCell111133113100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH thetaBelowCell111133113100))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHH
            thetaBelowCell111133113100)))
            (by
              have h : (thetaBelowCell1111331131003100).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003100 h)
            (by
              have h : (thetaBelowCell1111331131003101).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003101 h)
            (by
              have h : (thetaBelowCell1111331131003102).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003102 h)
            (by
              have h : (thetaBelowCell1111331131003103).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003103 h))
        (by
          exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHH
            thetaBelowCell111133113100)))
            (by
              have h : (thetaBelowCell1111331131003110).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003110 h)
            (by
              have h : (thetaBelowCell1111331131003111).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003111 h)
            (by
              have h : (thetaBelowCell1111331131003112).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003112 h)
            (by
              have h : (thetaBelowCell1111331131003113).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131003113 h))
        (by
          have h : ((childHL (childLH (childHH thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH
            thetaBelowCell111133113100))) h)
        (by
          have h : ((childHH (childLH (childHH thetaBelowCell111133113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHH
            thetaBelowCell111133113100))) h))
    (by
      have h : ((childHL (childHH thetaBelowCell111133113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH thetaBelowCell111133113100)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell111133113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH thetaBelowCell111133113100)) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells47753ffbe9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells47753ffbe9

open CertificateCells47753ffbe9

theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c0 :
    adaptiveCoverCheck 6 thetaBelowCell111133113100 = true :=
  adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113100
    e24KC2ThetaBelowLeaf111133113_c1_c0_c0_c0 e24KC2ThetaBelowLeaf111133113_c1_c0_c0_c1
      e24KC2ThetaBelowLeaf111133113_c1_c0_c0_c2 e24KC2ThetaBelowLeaf111133113_c1_c0_c0_c3

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

namespace CertificateCellse21bcf4574

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse21bcf4574

open CertificateCellse21bcf4574
theorem e24KC2ThetaAboveLeaf0000220021_c0_c1_c0 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022002101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022002101)
    (by
      have h : ((childLL (childLL thetaAboveCell000022002101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL thetaAboveCell000022002101)) h)
    (by
      have h : ((childLH (childLL thetaAboveCell000022002101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL thetaAboveCell000022002101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022002101))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022002101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022002101))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022002101))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022002101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
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

namespace CertificateCellsda9a873863

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsda9a873863

open CertificateCellsda9a873863
theorem e24KC2ThetaAboveLeaf0000220021_c0_c2 :
    adaptiveCoverCheck 7 thetaAboveCell000022002102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002102
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022002102)
        (by
          have h : ((childLL (childLL thetaAboveCell000022002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022002102)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022002102)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022002102)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022002102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022002102)
        (by
          have h : ((childLL (childLH thetaAboveCell000022002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022002102)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022002102)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022002102)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022002102)) h))
    (by
      have h : ((childHL thetaAboveCell000022002102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022002102) h)
    (by
      have h : ((childHH thetaAboveCell000022002102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022002102) h)

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

namespace CertificateCells7d865d7559

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells7d865d7559

open CertificateCells7d865d7559
theorem cover_subtree_6a2ae51f01eb :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113000 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113000
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113000)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113000)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131113000)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131113000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131113000)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131113000)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131113000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131113000)) h))

theorem cover_subtree_a45c44028853 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113001 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113001
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113001)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113001)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131113001)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131113001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131113001)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131113001)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131113001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131113001)) h))

theorem cover_subtree_d2590f3569cd :
    adaptiveCoverCheck 3 (childLL (childLL (childHH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHH
    thetaBelowCell111133113111)))
    cover_subtree_6a2ae51f01eb
    cover_subtree_a45c44028853
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113002
        (by
          have h : ((childLL thetaBelowCell1111331131113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131113002) h)
        (by
          have h : ((childLH thetaBelowCell1111331131113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131113002) h)
        (by
          have h : ((childHL thetaBelowCell1111331131113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131113002) h)
        (by
          have h : ((childHH thetaBelowCell1111331131113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131113002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113003
        (by
          have h : ((childLL thetaBelowCell1111331131113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131113003) h)
        (by
          have h : ((childLH thetaBelowCell1111331131113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131113003) h)
        (by
          have h : ((childHL thetaBelowCell1111331131113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131113003) h)
        (by
          have h : ((childHH thetaBelowCell1111331131113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131113003) h))

theorem cover_subtree_903db5f2747c :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113010 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113010
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113010)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113010)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131113010)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131113010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131113010)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131113010)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131113010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131113010)) h))

theorem cover_subtree_4ba95efb8e56 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131113011 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113011
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLL thetaBelowCell1111331131113011)
        (by
          have h : ((childLL (childLL thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLL
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLL
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLL
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLL
            thetaBelowCell1111331131113011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113011)
        (by
          have h : ((childLL (childLH thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
            thetaBelowCell1111331131113011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131113011)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131113011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131113011)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131113011)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131113011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131113011)) h))

theorem cover_subtree_189c3ed220c3 :
    adaptiveCoverCheck 3 (childLH (childLL (childHH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHH
    thetaBelowCell111133113111)))
    cover_subtree_903db5f2747c
    cover_subtree_4ba95efb8e56
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113012
        (by
          have h : ((childLL thetaBelowCell1111331131113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131113012) h)
        (by
          have h : ((childLH thetaBelowCell1111331131113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131113012) h)
        (by
          have h : ((childHL thetaBelowCell1111331131113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131113012) h)
        (by
          have h : ((childHH thetaBelowCell1111331131113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131113012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131113013
        (by
          have h : ((childLL thetaBelowCell1111331131113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131113013) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 0 (childLH thetaBelowCell1111331131113013)
            (by
              have h : ((childLL (childLH thetaBelowCell1111331131113013))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childLH
                thetaBelowCell1111331131113013)) h)
            (by
              have h : ((childLH (childLH thetaBelowCell1111331131113013))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childLH
                thetaBelowCell1111331131113013)) h)
            (by
              have h : ((childHL (childLH thetaBelowCell1111331131113013))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childLH
                thetaBelowCell1111331131113013)) h)
            (by
              have h : ((childHH (childLH thetaBelowCell1111331131113013))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childLH
                thetaBelowCell1111331131113013)) h))
        (by
          have h : ((childHL thetaBelowCell1111331131113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131113013) h)
        (by
          have h : ((childHH thetaBelowCell1111331131113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131113013) h))

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3_c0 :
    adaptiveCoverCheck 4 (childLL (childHH thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH thetaBelowCell111133113111))
    cover_subtree_d2590f3569cd
    cover_subtree_189c3ed220c3
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childLL (childHH
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113020 h)
        (by
          have h : (thetaBelowCell1111331131113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113021 h)
        (by
          have h : (thetaBelowCell1111331131113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113022 h)
        (by
          have h : (thetaBelowCell1111331131113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLL (childHH
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113030 h)
        (by
          have h : (thetaBelowCell1111331131113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113031 h)
        (by
          have h : (thetaBelowCell1111331131113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113032 h)
        (by
          have h : (thetaBelowCell1111331131113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131113033 h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsca42d19ac6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsca42d19ac6

open CertificateCellsca42d19ac6

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133113111) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133113111)
    e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3_c0 e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3_c1
      e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3_c2 e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3_c3

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

namespace CertificateCells257a1a1faa

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells257a1a1faa

open CertificateCells257a1a1faa
theorem cover_subtree_596b54980499 :
    adaptiveCoverCheck 4 (childHL (childLL thetaBelowCell111133113101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133113101))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLL
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131010200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010200 h)
        (by
          have h : (thetaBelowCell1111331131010201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010201 h)
        (by
          have h : (thetaBelowCell1111331131010202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010202 h)
        (by
          have h : (thetaBelowCell1111331131010203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131010210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010210 h)
        (by
          have h : (thetaBelowCell1111331131010211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010211 h)
        (by
          have h : (thetaBelowCell1111331131010212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010212 h)
        (by
          have h : (thetaBelowCell1111331131010213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010213 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131010220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010220 h)
        (by
          have h : (thetaBelowCell1111331131010221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010221 h)
        (by
          have h : (thetaBelowCell1111331131010222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010222 h)
        (by
          have h : (thetaBelowCell1111331131010223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131010230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010230 h)
        (by
          have h : (thetaBelowCell1111331131010231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010231 h)
        (by
          have h : (thetaBelowCell1111331131010232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010232 h)
        (by
          have h : (thetaBelowCell1111331131010233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010233 h))

theorem cover_subtree_e230aaf0d2f3 :
    adaptiveCoverCheck 4 (childHH (childLL thetaBelowCell111133113101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133113101))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131010300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010300 h)
        (by
          have h : (thetaBelowCell1111331131010301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010301 h)
        (by
          have h : (thetaBelowCell1111331131010302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010302 h)
        (by
          have h : (thetaBelowCell1111331131010303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131010310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010310 h)
        (by
          have h : (thetaBelowCell1111331131010311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010311 h)
        (by
          have h : (thetaBelowCell1111331131010312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010312 h)
        (by
          have h : (thetaBelowCell1111331131010313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010313 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131010320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010320 h)
        (by
          have h : (thetaBelowCell1111331131010321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010321 h)
        (by
          have h : (thetaBelowCell1111331131010322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010322 h)
        (by
          have h : (thetaBelowCell1111331131010323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131010330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010330 h)
        (by
          have h : (thetaBelowCell1111331131010331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010331 h)
        (by
          have h : (thetaBelowCell1111331131010332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010332 h)
        (by
          have h : (thetaBelowCell1111331131010333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131010333 h))

theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c1_c0 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133113101) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113101)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133113101))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133113101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133113101))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133113101))) h))
    cover_subtree_596b54980499
    cover_subtree_e230aaf0d2f3

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

namespace CertificateCellsb187906d24

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb187906d24

open CertificateCellsb187906d24
theorem cover_subtree_504c637fe057 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012002 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012002
    (by
      have h : ((childLL thetaAboveCell0000220021012002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012002) h)
    (by
      have h : ((childLH thetaAboveCell0000220021012002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012002) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021012002)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021012002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021012002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021012002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021012002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021012002)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021012002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021012002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021012002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021012002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021012002)) h))

theorem cover_subtree_2a357587fe2c :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012003 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012003
    (by
      have h : ((childLL thetaAboveCell0000220021012003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012003) h)
    (by
      have h : ((childLH thetaAboveCell0000220021012003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012003) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021012003)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021012003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021012003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021012003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021012003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021012003)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021012003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021012003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021012003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021012003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021012003)) h))

theorem cover_subtree_e90aeadfa33e :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
    thetaAboveCell000022002101)))
    (by
      have h : (thetaAboveCell0000220021012000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012000 h)
    (by
      have h : (thetaAboveCell0000220021012001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012001 h)
    cover_subtree_504c637fe057
    cover_subtree_2a357587fe2c

theorem cover_subtree_fb92afbe7b07 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012012 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012012
    (by
      have h : ((childLL thetaAboveCell0000220021012012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012012) h)
    (by
      have h : ((childLH thetaAboveCell0000220021012012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012012) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021012012)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021012012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021012012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021012012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021012012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021012012)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021012012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021012012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021012012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021012012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021012012)) h))

theorem cover_subtree_0e32fa63735b :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
    thetaAboveCell000022002101)))
    (by
      have h : (thetaAboveCell0000220021012010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012010 h)
    (by
      have h : (thetaAboveCell0000220021012011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021012011 h)
    cover_subtree_fb92afbe7b07
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012013
        (by
          have h : ((childLL thetaAboveCell0000220021012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012013) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012013) h)
        (by
          exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021012013)
            (by
              have h : ((childLL (childHL thetaAboveCell0000220021012013))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
                thetaAboveCell0000220021012013)) h)
            (by
              have h : ((childLH (childHL thetaAboveCell0000220021012013))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
                thetaAboveCell0000220021012013)) h)
            (by
              have h : ((childHL (childHL thetaAboveCell0000220021012013))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
                thetaAboveCell0000220021012013)) h)
            (by
              have h : ((childHH (childHL thetaAboveCell0000220021012013))).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
                thetaAboveCell0000220021012013)) h))
        (by
          have h : ((childHH thetaAboveCell0000220021012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012013) h))

theorem cover_subtree_2d2c3f59bbe5 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012020 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012020
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021012020)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021012020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021012020)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021012020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021012020)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021012020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021012020)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021012020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021012020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021012020)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021012020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021012020)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021012020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021012020)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021012020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021012020)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021012020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021012020)) h))
    (by
      have h : ((childHL thetaAboveCell0000220021012020)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012020) h)
    (by
      have h : ((childHH thetaAboveCell0000220021012020)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012020) h)

theorem cover_subtree_118ca13c27e0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012021 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012021
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021012021)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021012021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021012021)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021012021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021012021)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021012021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021012021)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021012021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021012021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021012021)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021012021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021012021)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021012021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021012021)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021012021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021012021)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021012021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021012021)) h))
    (by
      have h : ((childHL thetaAboveCell0000220021012021)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012021) h)
    (by
      have h : ((childHH thetaAboveCell0000220021012021)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012021) h)

theorem cover_subtree_1582f7d2c473 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022002101)))
    cover_subtree_2d2c3f59bbe5
    cover_subtree_118ca13c27e0
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012022
        (by
          have h : ((childLL thetaAboveCell0000220021012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012022) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012022) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012022) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012023
        (by
          have h : ((childLL thetaAboveCell0000220021012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012023) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012023) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012023) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012023) h))

theorem cover_subtree_b689532944b1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012030 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012030
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021012030)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021012030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021012030)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021012030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021012030)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021012030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021012030)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021012030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021012030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021012030)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021012030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021012030)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021012030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021012030)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021012030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021012030)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021012030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021012030)) h))
    (by
      have h : ((childHL thetaAboveCell0000220021012030)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012030) h)
    (by
      have h : ((childHH thetaAboveCell0000220021012030)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012030) h)

theorem cover_subtree_229b7653f1bc :
    adaptiveCoverCheck 3 thetaAboveCell0000220021012031 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012031
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021012031)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021012031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021012031)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021012031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021012031)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021012031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021012031)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021012031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021012031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021012031)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021012031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021012031)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021012031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021012031)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021012031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021012031)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021012031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021012031)) h))
    (by
      have h : ((childHL thetaAboveCell0000220021012031)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012031) h)
    (by
      have h : ((childHH thetaAboveCell0000220021012031)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012031) h)

theorem cover_subtree_b1c2b8600845 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022002101)))
    cover_subtree_b689532944b1
    cover_subtree_229b7653f1bc
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012032
        (by
          have h : ((childLL thetaAboveCell0000220021012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012032) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012032) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012032) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021012033
        (by
          have h : ((childLL thetaAboveCell0000220021012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021012033) h)
        (by
          have h : ((childLH thetaAboveCell0000220021012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021012033) h)
        (by
          have h : ((childHL thetaAboveCell0000220021012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021012033) h)
        (by
          have h : ((childHH thetaAboveCell0000220021012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021012033) h))

theorem e24KC2ThetaAboveLeaf0000220021_c0_c1_c2_c0 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002101))
    cover_subtree_e90aeadfa33e
    cover_subtree_0e32fa63735b
    cover_subtree_1582f7d2c473
    cover_subtree_b1c2b8600845

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellseb98bd469c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellseb98bd469c

open CertificateCellseb98bd469c

theorem e24KC2ThetaAboveLeaf0000220021_c0_c1_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002101) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002101)
    e24KC2ThetaAboveLeaf0000220021_c0_c1_c2_c0 e24KC2ThetaAboveLeaf0000220021_c0_c1_c2_c1
      e24KC2ThetaAboveLeaf0000220021_c0_c1_c2_c2 e24KC2ThetaAboveLeaf0000220021_c0_c1_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0fb8590a1f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0fb8590a1f

open CertificateCells0fb8590a1f

theorem e24KC2ThetaAboveLeaf0000220021_c0_c1 :
    adaptiveCoverCheck 7 thetaAboveCell000022002101 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002101
    e24KC2ThetaAboveLeaf0000220021_c0_c1_c0 e24KC2ThetaAboveLeaf0000220021_c0_c1_c1
      e24KC2ThetaAboveLeaf0000220021_c0_c1_c2 e24KC2ThetaAboveLeaf0000220021_c0_c1_c3

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

namespace CertificateCells21614274e2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells21614274e2

open CertificateCells21614274e2
theorem e24KC2ThetaBelowLeaf111133113_c1_c3 :
    adaptiveCoverCheck 7 (childHH (childLH (childHH thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLH (childHH thetaBelowCell11113311)))
    (by
      have h : (thetaBelowCell111133113130).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113130 h)
    (by
      have h : (thetaBelowCell111133113131).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113131 h)
    (by
      have h : (thetaBelowCell111133113132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113132 h)
    (by
      have h : (thetaBelowCell111133113133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113133 h)

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

namespace CertificateCells075667848d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells075667848d

open CertificateCells075667848d
theorem cover_subtree_162fb6940e90 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002102 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002102
    (by
      have h : ((childLL thetaAboveCell0000220021002102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002102) h)
    (by
      have h : ((childLH thetaAboveCell0000220021002102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002102) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002102)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002102)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002102)) h))

theorem cover_subtree_2b38e4b2557d :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002103 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002103
    (by
      have h : ((childLL thetaAboveCell0000220021002103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002103) h)
    (by
      have h : ((childLH thetaAboveCell0000220021002103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002103) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002103)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002103)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002103)) h))

theorem cover_subtree_ee2829c05e95 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021002100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002100 h)
    (by
      have h : (thetaAboveCell0000220021002101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002101 h)
    cover_subtree_162fb6940e90
    cover_subtree_2b38e4b2557d

theorem cover_subtree_d302433685b0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002112 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002112
    (by
      have h : ((childLL thetaAboveCell0000220021002112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002112) h)
    (by
      have h : ((childLH thetaAboveCell0000220021002112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002112) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002112)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002112)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002112)) h))

theorem cover_subtree_549e46a5d3e3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002113 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002113
    (by
      have h : ((childLL thetaAboveCell0000220021002113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002113) h)
    (by
      have h : ((childLH thetaAboveCell0000220021002113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002113) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002113)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002113)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002113)) h))

theorem cover_subtree_4c9680a92e0c :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021002110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002110 h)
    (by
      have h : (thetaAboveCell0000220021002111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021002111 h)
    cover_subtree_d302433685b0
    cover_subtree_549e46a5d3e3

theorem cover_subtree_78071866416e :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002120 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002120
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021002120)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021002120)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021002120)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021002120)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002120)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002120)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002120)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002120)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002120))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002120)) h))

theorem cover_subtree_088dc6ec9713 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002121 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002121
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021002121)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021002121)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021002121)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021002121)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002121)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002121)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002121)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002121)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002121))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002121)) h))

theorem cover_subtree_e0b48be7f1b2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022002100)))
    cover_subtree_78071866416e
    cover_subtree_088dc6ec9713
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002122
        (by
          have h : ((childLL thetaAboveCell0000220021002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002122) h)
        (by
          have h : ((childLH thetaAboveCell0000220021002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002122) h)
        (by
          have h : ((childHL thetaAboveCell0000220021002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021002122) h)
        (by
          have h : ((childHH thetaAboveCell0000220021002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021002122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002123
        (by
          have h : ((childLL thetaAboveCell0000220021002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002123) h)
        (by
          have h : ((childLH thetaAboveCell0000220021002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002123) h)
        (by
          have h : ((childHL thetaAboveCell0000220021002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021002123) h)
        (by
          have h : ((childHH thetaAboveCell0000220021002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021002123) h))

theorem cover_subtree_cb8fede25e6d :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002130 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002130
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021002130)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021002130)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021002130)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021002130)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002130)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002130)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002130)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002130)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002130))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002130)) h))

theorem cover_subtree_9df38978a25b :
    adaptiveCoverCheck 3 thetaAboveCell0000220021002131 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002131
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021002131)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021002131)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021002131)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021002131)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021002131)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021002131)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021002131)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021002131)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021002131))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021002131)) h))

theorem cover_subtree_413edc037905 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022002100)))
    cover_subtree_cb8fede25e6d
    cover_subtree_9df38978a25b
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002132
        (by
          have h : ((childLL thetaAboveCell0000220021002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002132) h)
        (by
          have h : ((childLH thetaAboveCell0000220021002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002132) h)
        (by
          have h : ((childHL thetaAboveCell0000220021002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021002132) h)
        (by
          have h : ((childHH thetaAboveCell0000220021002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021002132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021002133
        (by
          have h : ((childLL thetaAboveCell0000220021002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021002133) h)
        (by
          have h : ((childLH thetaAboveCell0000220021002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021002133) h)
        (by
          have h : ((childHL thetaAboveCell0000220021002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021002133) h)
        (by
          have h : ((childHH thetaAboveCell0000220021002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021002133) h))

theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c2_c1 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002100))
    cover_subtree_ee2829c05e95
    cover_subtree_4c9680a92e0c
    cover_subtree_e0b48be7f1b2
    cover_subtree_413edc037905

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells135b119fc2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells135b119fc2

open CertificateCells135b119fc2

theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002100) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002100)
    e24KC2ThetaAboveLeaf0000220021_c0_c0_c2_c0 e24KC2ThetaAboveLeaf0000220021_c0_c0_c2_c1
      e24KC2ThetaAboveLeaf0000220021_c0_c0_c2_c2 e24KC2ThetaAboveLeaf0000220021_c0_c0_c2_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse53a016898

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse53a016898

open CertificateCellse53a016898

theorem e24KC2ThetaAboveLeaf0000220021_c0_c0 :
    adaptiveCoverCheck 7 thetaAboveCell000022002100 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002100
    e24KC2ThetaAboveLeaf0000220021_c0_c0_c0 e24KC2ThetaAboveLeaf0000220021_c0_c0_c1
      e24KC2ThetaAboveLeaf0000220021_c0_c0_c2 e24KC2ThetaAboveLeaf0000220021_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8b72842cc0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells8b72842cc0

open CertificateCells8b72842cc0

theorem e24KC2ThetaAboveLeaf0000220021_c0 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00002200))) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00002200)))
    e24KC2ThetaAboveLeaf0000220021_c0_c0 e24KC2ThetaAboveLeaf0000220021_c0_c1
      e24KC2ThetaAboveLeaf0000220021_c0_c2 e24KC2ThetaAboveLeaf0000220021_c0_c3

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

namespace CertificateCells3d04a04d91

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3d04a04d91

open CertificateCells3d04a04d91
theorem e24KC2ThetaBelowLeaf111133113_c0_c3 :
    adaptiveCoverCheck 7 (childHH (childLL (childHH thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHH (childLL (childHH thetaBelowCell11113311)))
    (by
      have h : (thetaBelowCell111133113030).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113030 h)
    (by
      have h : (thetaBelowCell111133113031).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113031 h)
    (by
      have h : (thetaBelowCell111133113032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113032 h)
    (by
      have h : (thetaBelowCell111133113033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113033 h)

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

namespace CertificateCells665e67ba22

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells665e67ba22

open CertificateCells665e67ba22
theorem cover_subtree_1c545d2d332e :
    adaptiveCoverCheck 3 (childLH (childLL (childHH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHH
    thetaBelowCell111133113101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131013010
        (by
          have h : ((childLL thetaBelowCell1111331131013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131013010) h)
        (by
          have h : ((childLH thetaBelowCell1111331131013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131013010) h)
        (by
          have h : ((childHL thetaBelowCell1111331131013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131013010) h)
        (by
          have h : ((childHH thetaBelowCell1111331131013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131013010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131013011
        (by
          have h : ((childLL thetaBelowCell1111331131013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131013011) h)
        (by
          have h : ((childLH thetaBelowCell1111331131013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131013011) h)
        (by
          have h : ((childHL thetaBelowCell1111331131013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131013011) h)
        (by
          have h : ((childHH thetaBelowCell1111331131013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131013011) h))
    (by
      have h : (thetaBelowCell1111331131013012).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013012 h)
    (by
      have h : (thetaBelowCell1111331131013013).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013013 h)

theorem cover_subtree_a6892a976bdc :
    adaptiveCoverCheck 4 (childLL (childHH thetaBelowCell111133113101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH thetaBelowCell111133113101))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHH
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131013000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013000 h)
        (by
          have h : (thetaBelowCell1111331131013001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013001 h)
        (by
          have h : (thetaBelowCell1111331131013002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013002 h)
        (by
          have h : (thetaBelowCell1111331131013003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013003 h))
    cover_subtree_1c545d2d332e
    (by
      have h : ((childHL (childLL (childHH thetaBelowCell111133113101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH
        thetaBelowCell111133113101))) h)
    (by
      have h : ((childHH (childLL (childHH thetaBelowCell111133113101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH
        thetaBelowCell111133113101))) h)

theorem cover_subtree_8f27cd7d62f9 :
    adaptiveCoverCheck 3 (childLL (childLH (childHH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHH
    thetaBelowCell111133113101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131013100
        (by
          have h : ((childLL thetaBelowCell1111331131013100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131013100) h)
        (by
          have h : ((childLH thetaBelowCell1111331131013100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131013100) h)
        (by
          have h : ((childHL thetaBelowCell1111331131013100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131013100) h)
        (by
          have h : ((childHH thetaBelowCell1111331131013100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131013100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131013101
        (by
          have h : ((childLL thetaBelowCell1111331131013101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131013101) h)
        (by
          have h : ((childLH thetaBelowCell1111331131013101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131013101) h)
        (by
          have h : ((childHL thetaBelowCell1111331131013101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131013101) h)
        (by
          have h : ((childHH thetaBelowCell1111331131013101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131013101) h))
    (by
      have h : (thetaBelowCell1111331131013102).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013102 h)
    (by
      have h : (thetaBelowCell1111331131013103).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013103 h)

theorem cover_subtree_3a8993d4b677 :
    adaptiveCoverCheck 3 (childLH (childLH (childHH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHH
    thetaBelowCell111133113101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131013110
        (by
          have h : ((childLL thetaBelowCell1111331131013110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131013110) h)
        (by
          have h : ((childLH thetaBelowCell1111331131013110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131013110) h)
        (by
          have h : ((childHL thetaBelowCell1111331131013110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131013110) h)
        (by
          have h : ((childHH thetaBelowCell1111331131013110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131013110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131013111
        (by
          have h : ((childLL thetaBelowCell1111331131013111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131013111) h)
        (by
          have h : ((childLH thetaBelowCell1111331131013111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131013111) h)
        (by
          have h : ((childHL thetaBelowCell1111331131013111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131013111) h)
        (by
          have h : ((childHH thetaBelowCell1111331131013111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131013111) h))
    (by
      have h : (thetaBelowCell1111331131013112).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013112 h)
    (by
      have h : (thetaBelowCell1111331131013113).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131013113 h)

theorem cover_subtree_f225800535b1 :
    adaptiveCoverCheck 4 (childLH (childHH thetaBelowCell111133113101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH thetaBelowCell111133113101))
    cover_subtree_8f27cd7d62f9
    cover_subtree_3a8993d4b677
    (by
      have h : ((childHL (childLH (childHH thetaBelowCell111133113101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH
        thetaBelowCell111133113101))) h)
    (by
      have h : ((childHH (childLH (childHH thetaBelowCell111133113101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childHH
        thetaBelowCell111133113101))) h)

theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c1_c3 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133113101) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133113101)
    cover_subtree_a6892a976bdc
    cover_subtree_f225800535b1
    (by
      have h : ((childHL (childHH thetaBelowCell111133113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH thetaBelowCell111133113101)) h)
    (by
      have h : ((childHH (childHH thetaBelowCell111133113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH thetaBelowCell111133113101)) h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa275032fe9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa275032fe9

open CertificateCellsa275032fe9

theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c1 :
    adaptiveCoverCheck 6 thetaBelowCell111133113101 = true :=
  adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113101
    e24KC2ThetaBelowLeaf111133113_c1_c0_c1_c0 e24KC2ThetaBelowLeaf111133113_c1_c0_c1_c1
      e24KC2ThetaBelowLeaf111133113_c1_c0_c1_c2 e24KC2ThetaBelowLeaf111133113_c1_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells09124dcbf9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells09124dcbf9

open CertificateCells09124dcbf9

theorem e24KC2ThetaBelowLeaf111133113_c1_c0 :
    adaptiveCoverCheck 7 (childLL (childLH (childHH thetaBelowCell11113311))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLL (childLH (childHH thetaBelowCell11113311)))
    e24KC2ThetaBelowLeaf111133113_c1_c0_c0 e24KC2ThetaBelowLeaf111133113_c1_c0_c1
      e24KC2ThetaBelowLeaf111133113_c1_c0_c2 e24KC2ThetaBelowLeaf111133113_c1_c0_c3

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

namespace CertificateCellse133bf0420

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse133bf0420

open CertificateCellse133bf0420
theorem cover_subtree_8c4e3e00c778 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHL
    thetaAboveCell000022002110)))
    (by
      have h : (thetaAboveCell0000220021102000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102000 h)
    (by
      have h : (thetaAboveCell0000220021102001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102002
        (by
          have h : ((childLL thetaAboveCell0000220021102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102002) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102002) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102002) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102003
        (by
          have h : ((childLL thetaAboveCell0000220021102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102003) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102003) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102003) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102003) h))

theorem cover_subtree_49f6eb3ee7e0 :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHL
    thetaAboveCell000022002110)))
    (by
      have h : (thetaAboveCell0000220021102010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102010 h)
    (by
      have h : (thetaAboveCell0000220021102011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102012
        (by
          have h : ((childLL thetaAboveCell0000220021102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102012) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102012) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102012) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102013
        (by
          have h : ((childLL thetaAboveCell0000220021102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102013) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102013) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102013) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102013) h))

theorem cover_subtree_adebd26c440a :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
    thetaAboveCell000022002110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102020
        (by
          have h : ((childLL thetaAboveCell0000220021102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102020) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102020) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102020) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102021
        (by
          have h : ((childLL thetaAboveCell0000220021102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102021) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102021) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102021) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102022
        (by
          have h : ((childLL thetaAboveCell0000220021102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102022) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102022) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102022) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102023
        (by
          have h : ((childLL thetaAboveCell0000220021102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102023) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102023) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102023) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102023) h))

theorem cover_subtree_cfe74f698d24 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
    thetaAboveCell000022002110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102030
        (by
          have h : ((childLL thetaAboveCell0000220021102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102030) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102030) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102030) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102031
        (by
          have h : ((childLL thetaAboveCell0000220021102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102031) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102031) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102031) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102032
        (by
          have h : ((childLL thetaAboveCell0000220021102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102032) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102032) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102032) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102033
        (by
          have h : ((childLL thetaAboveCell0000220021102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102033) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102033) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102033) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102033) h))

theorem cover_subtree_64b5e3c15e8d :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022002110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022002110))
    cover_subtree_8c4e3e00c778
    cover_subtree_49f6eb3ee7e0
    cover_subtree_adebd26c440a
    cover_subtree_cfe74f698d24

theorem cover_subtree_aeac3ba6168f :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH (childHL
    thetaAboveCell000022002110)))
    (by
      have h : (thetaAboveCell0000220021102100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102100 h)
    (by
      have h : (thetaAboveCell0000220021102101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102102
        (by
          have h : ((childLL thetaAboveCell0000220021102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102102) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102102) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102102) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102103
        (by
          have h : ((childLL thetaAboveCell0000220021102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102103) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102103) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102103) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102103) h))

theorem cover_subtree_325d50012465 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH (childHL
    thetaAboveCell000022002110)))
    (by
      have h : (thetaAboveCell0000220021102110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102110 h)
    (by
      have h : (thetaAboveCell0000220021102111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102112
        (by
          have h : ((childLL thetaAboveCell0000220021102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102112) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102112) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102112) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102113
        (by
          have h : ((childLL thetaAboveCell0000220021102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102113) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102113) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102113) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102113) h))

theorem cover_subtree_b265451cd007 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
    thetaAboveCell000022002110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102120
        (by
          have h : ((childLL thetaAboveCell0000220021102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102120) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102120) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102120) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102121
        (by
          have h : ((childLL thetaAboveCell0000220021102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102121) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102121) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102121) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102122
        (by
          have h : ((childLL thetaAboveCell0000220021102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102122) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102122) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102122) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102123
        (by
          have h : ((childLL thetaAboveCell0000220021102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102123) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102123) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102123) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102123) h))

theorem cover_subtree_613b8841c9c0 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
    thetaAboveCell000022002110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102130
        (by
          have h : ((childLL thetaAboveCell0000220021102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102130) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102130) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102130) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102131
        (by
          have h : ((childLL thetaAboveCell0000220021102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102131) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102131) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102131) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102132
        (by
          have h : ((childLL thetaAboveCell0000220021102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102132) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102132) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102132) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021102133
        (by
          have h : ((childLL thetaAboveCell0000220021102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021102133) h)
        (by
          have h : ((childLH thetaAboveCell0000220021102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021102133) h)
        (by
          have h : ((childHL thetaAboveCell0000220021102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021102133) h)
        (by
          have h : ((childHH thetaAboveCell0000220021102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021102133) h))

theorem cover_subtree_52c3ab758725 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022002110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022002110))
    cover_subtree_aeac3ba6168f
    cover_subtree_325d50012465
    cover_subtree_b265451cd007
    cover_subtree_613b8841c9c0

theorem cover_subtree_1c021cc633a3 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022002110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022002110)))
        (by
          have h : (thetaAboveCell0000220021102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102200 h)
        (by
          have h : (thetaAboveCell0000220021102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102201 h)
        (by
          have h : (thetaAboveCell0000220021102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102202 h)
        (by
          have h : (thetaAboveCell0000220021102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022002110)))
        (by
          have h : (thetaAboveCell0000220021102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102210 h)
        (by
          have h : (thetaAboveCell0000220021102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102211 h)
        (by
          have h : (thetaAboveCell0000220021102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102212 h)
        (by
          have h : (thetaAboveCell0000220021102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022002110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022002110))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022002110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022002110))) h)

theorem cover_subtree_191cbd679a04 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022002110))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022002110)))
        (by
          have h : (thetaAboveCell0000220021102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102300 h)
        (by
          have h : (thetaAboveCell0000220021102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102301 h)
        (by
          have h : (thetaAboveCell0000220021102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102302 h)
        (by
          have h : (thetaAboveCell0000220021102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022002110)))
        (by
          have h : (thetaAboveCell0000220021102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102310 h)
        (by
          have h : (thetaAboveCell0000220021102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102311 h)
        (by
          have h : (thetaAboveCell0000220021102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102312 h)
        (by
          have h : (thetaAboveCell0000220021102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021102313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022002110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022002110))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022002110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022002110))) h)

theorem e24KC2ThetaAboveLeaf0000220021_c1_c0_c2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022002110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022002110)
    cover_subtree_64b5e3c15e8d
    cover_subtree_52c3ab758725
    cover_subtree_1c021cc633a3
    cover_subtree_191cbd679a04

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf1833757d0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsf1833757d0

open CertificateCellsf1833757d0

theorem e24KC2ThetaAboveLeaf0000220021_c1_c0 :
    adaptiveCoverCheck 7 thetaAboveCell000022002110 = true :=
  adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002110
    e24KC2ThetaAboveLeaf0000220021_c1_c0_c0 e24KC2ThetaAboveLeaf0000220021_c1_c0_c1
      e24KC2ThetaAboveLeaf0000220021_c1_c0_c2 e24KC2ThetaAboveLeaf0000220021_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells21f94a2daf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells21f94a2daf

open CertificateCells21f94a2daf

theorem e24KC2ThetaAboveLeaf0000220021_c1 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00002200))) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00002200)))
    e24KC2ThetaAboveLeaf0000220021_c1_c0 e24KC2ThetaAboveLeaf0000220021_c1_c1
      e24KC2ThetaAboveLeaf0000220021_c1_c2 e24KC2ThetaAboveLeaf0000220021_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsbb4f00460c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsbb4f00460c

open CertificateCellsbb4f00460c

theorem e24KC2ThetaAboveLeaf0000220021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00002200)) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00002200))
    e24KC2ThetaAboveLeaf0000220021_c0 e24KC2ThetaAboveLeaf0000220021_c1
      e24KC2ThetaAboveLeaf0000220021_c2 e24KC2ThetaAboveLeaf0000220021_c3

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

namespace CertificateCells232e7e9a76

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells232e7e9a76

open CertificateCells232e7e9a76
theorem e24KC2ThetaBelowLeaf111133113_c0_c2 :
    adaptiveCoverCheck 7 (childHL (childLL (childHH thetaBelowCell11113311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 6 (childHL (childLL (childHH thetaBelowCell11113311)))
    (by
      have h : (thetaBelowCell111133113020).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113020 h)
    (by
      have h : (thetaBelowCell111133113021).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113021 h)
    (by
      have h : (thetaBelowCell111133113022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113022 h)
    (by
      have h : (thetaBelowCell111133113023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 thetaBelowCell111133113023 h)

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse657ecadb5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse657ecadb5

open CertificateCellse657ecadb5

theorem e24KC2ThetaBelowLeaf111133113_c0 :
    adaptiveCoverCheck 8 (childLL (childHH thetaBelowCell11113311)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childLL (childHH thetaBelowCell11113311))
    e24KC2ThetaBelowLeaf111133113_c0_c0 e24KC2ThetaBelowLeaf111133113_c0_c1
      e24KC2ThetaBelowLeaf111133113_c0_c2 e24KC2ThetaBelowLeaf111133113_c0_c3

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

namespace CertificateCells78b824f474

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells78b824f474

open CertificateCells78b824f474
theorem cover_subtree_7d1a4629139c :
    adaptiveCoverCheck 3 (childHL (childHL (childLL thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLL
    thetaBelowCell111133113111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110220
        (by
          have h : ((childLL thetaBelowCell1111331131110220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110220) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110220) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110220) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110220)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110220) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110221
        (by
          have h : ((childLL thetaBelowCell1111331131110221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110221) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110221) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110221) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110221)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110221) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110222
        (by
          have h : ((childLL thetaBelowCell1111331131110222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110222) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110222) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110222) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110222) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110223
        (by
          have h : ((childLL thetaBelowCell1111331131110223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110223) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110223) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110223) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110223) h))

theorem cover_subtree_271c266eebff :
    adaptiveCoverCheck 3 (childHH (childHL (childLL thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLL
    thetaBelowCell111133113111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110230
        (by
          have h : ((childLL thetaBelowCell1111331131110230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110230) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110230) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110230) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110230)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110230) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110231
        (by
          have h : ((childLL thetaBelowCell1111331131110231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110231) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110231) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110231) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110231) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110232
        (by
          have h : ((childLL thetaBelowCell1111331131110232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110232) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110232) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110232) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110232) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110233
        (by
          have h : ((childLL thetaBelowCell1111331131110233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110233) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110233) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110233) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110233) h))

theorem cover_subtree_f2e98bb9d295 :
    adaptiveCoverCheck 4 (childHL (childLL thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL thetaBelowCell111133113111))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLL
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131110200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110200 h)
        (by
          have h : (thetaBelowCell1111331131110201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110201 h)
        (by
          have h : (thetaBelowCell1111331131110202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110202 h)
        (by
          have h : (thetaBelowCell1111331131110203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLL
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131110210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110210 h)
        (by
          have h : (thetaBelowCell1111331131110211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110211 h)
        (by
          have h : (thetaBelowCell1111331131110212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110212 h)
        (by
          have h : (thetaBelowCell1111331131110213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110213 h))
    cover_subtree_7d1a4629139c
    cover_subtree_271c266eebff

theorem cover_subtree_9fadcdfbc6fb :
    adaptiveCoverCheck 3 (childHL (childHH (childLL thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLL
    thetaBelowCell111133113111)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110320
        (by
          have h : ((childLL thetaBelowCell1111331131110320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110320) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110320) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110320) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110320) h))
    (by
      have h : (thetaBelowCell1111331131110321).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110321 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110322
        (by
          have h : ((childLL thetaBelowCell1111331131110322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110322) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110322) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110322) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110322) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110323
        (by
          have h : ((childLL thetaBelowCell1111331131110323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110323) h)
        (by
          have h : ((childLH thetaBelowCell1111331131110323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110323) h)
        (by
          have h : ((childHL thetaBelowCell1111331131110323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131110323) h)
        (by
          have h : ((childHH thetaBelowCell1111331131110323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131110323) h))

theorem cover_subtree_3e826769a774 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131110332 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110332
    (by
      have h : ((childLL thetaBelowCell1111331131110332)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110332) h)
    (by
      have h : ((childLH thetaBelowCell1111331131110332)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110332) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131110332)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131110332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131110332)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131110332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131110332)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131110332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131110332)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131110332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131110332)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131110332)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131110332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131110332)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131110332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131110332)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131110332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131110332)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131110332))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131110332)) h))

theorem cover_subtree_647c14158ebb :
    adaptiveCoverCheck 2 thetaBelowCell1111331131110333 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131110333
    (by
      have h : ((childLL thetaBelowCell1111331131110333)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131110333) h)
    (by
      have h : ((childLH thetaBelowCell1111331131110333)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131110333) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131110333)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131110333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131110333)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131110333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131110333)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131110333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131110333)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131110333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131110333)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131110333)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131110333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131110333)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131110333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131110333)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131110333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131110333)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131110333))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131110333)) h))

theorem cover_subtree_7bb13e3867b3 :
    adaptiveCoverCheck 3 (childHH (childHH (childLL thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLL
    thetaBelowCell111133113111)))
    (by
      have h : (thetaBelowCell1111331131110330).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110330 h)
    (by
      have h : (thetaBelowCell1111331131110331).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110331 h)
    cover_subtree_3e826769a774
    cover_subtree_647c14158ebb

theorem cover_subtree_108f8990274f :
    adaptiveCoverCheck 4 (childHH (childLL thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL thetaBelowCell111133113111))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLL
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131110300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110300 h)
        (by
          have h : (thetaBelowCell1111331131110301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110301 h)
        (by
          have h : (thetaBelowCell1111331131110302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110302 h)
        (by
          have h : (thetaBelowCell1111331131110303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLL
        thetaBelowCell111133113111)))
        (by
          have h : (thetaBelowCell1111331131110310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110310 h)
        (by
          have h : (thetaBelowCell1111331131110311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110311 h)
        (by
          have h : (thetaBelowCell1111331131110312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110312 h)
        (by
          have h : (thetaBelowCell1111331131110313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131110313 h))
    cover_subtree_9fadcdfbc6fb
    cover_subtree_7bb13e3867b3

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c0 :
    adaptiveCoverCheck 5 (childLL thetaBelowCell111133113111) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113111)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL thetaBelowCell111133113111))
        (by
          have h : ((childLL (childLL (childLL thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLL
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childLH (childLL (childLL thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLL
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childHL (childLL (childLL thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLL
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childHH (childLL (childLL thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLL
            thetaBelowCell111133113111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL thetaBelowCell111133113111))
        (by
          have h : ((childLL (childLH (childLL thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLL
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childLH (childLH (childLL thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLL
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childHL (childLH (childLL thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLL
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childHH (childLH (childLL thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLL
            thetaBelowCell111133113111))) h))
    cover_subtree_f2e98bb9d295
    cover_subtree_108f8990274f

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsccc2f90403

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsccc2f90403

open CertificateCellsccc2f90403

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1 :
    adaptiveCoverCheck 6 thetaBelowCell111133113111 = true :=
  adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113111
    e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c0 e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c1
      e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2 e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse5aa25a242

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse5aa25a242

open CertificateCellse5aa25a242

theorem e24KC2ThetaBelowLeaf111133113_c1_c1 :
    adaptiveCoverCheck 7 (childLH (childLH (childHH thetaBelowCell11113311))) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLH (childLH (childHH thetaBelowCell11113311)))
    e24KC2ThetaBelowLeaf111133113_c1_c1_c0 e24KC2ThetaBelowLeaf111133113_c1_c1_c1
      e24KC2ThetaBelowLeaf111133113_c1_c1_c2 e24KC2ThetaBelowLeaf111133113_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0d1c7d48ff

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0d1c7d48ff

open CertificateCells0d1c7d48ff

theorem e24KC2ThetaBelowLeaf111133113_c1 :
    adaptiveCoverCheck 8 (childLH (childHH thetaBelowCell11113311)) = true :=
  adaptiveCoverCheck_succ_of_children 7 (childLH (childHH thetaBelowCell11113311))
    e24KC2ThetaBelowLeaf111133113_c1_c0 e24KC2ThetaBelowLeaf111133113_c1_c1
      e24KC2ThetaBelowLeaf111133113_c1_c2 e24KC2ThetaBelowLeaf111133113_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 pure logical subtree join. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1d418dae20

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells1d418dae20

open CertificateCells1d418dae20

theorem e24KC2ThetaBelowLeaf111133113 :
    adaptiveCoverCheck 9 (childHH thetaBelowCell11113311) = true :=
  adaptiveCoverCheck_succ_of_children 8 (childHH thetaBelowCell11113311)
    e24KC2ThetaBelowLeaf111133113_c0 e24KC2ThetaBelowLeaf111133113_c1
      e24KC2ThetaBelowLeaf111133113_c2 e24KC2ThetaBelowLeaf111133113_c3

end PartE
end GerverSofa

end

end

end

end

end

end
