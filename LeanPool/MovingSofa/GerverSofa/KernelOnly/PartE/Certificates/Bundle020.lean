/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Bundle019
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch033`.
* `GerverSofa.KernelOnly.PartE.Certificates.Batch043`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCellsefec3b1324

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131111222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell111133113111)))

/-- Subcell `1111331131111333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131111333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell111133113111)))

end GerverSofa.PartE.CertificateCellsefec3b1324

namespace GerverSofa.PartE.CertificateCells11cd3db1c7

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131103000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell111133113110)))

/-- Subcell `1111331131103133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell111133113110)))

end GerverSofa.PartE.CertificateCells11cd3db1c7

namespace GerverSofa.PartE.CertificateCellse82c2dced4

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCellse82c2dced4

namespace GerverSofa.PartE.CertificateCells7a1b24c2da

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaBelowCell11113311)))

/-- Subcell `1111331131011220` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011221` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011222` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011223` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011230` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011231` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011232` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011233` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011200 : AngleCell :=
  childLL (childLL (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011201 : AngleCell :=
  childLH (childLL (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011202 : AngleCell :=
  childHL (childLL (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011203 : AngleCell :=
  childHH (childLL (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011210 : AngleCell :=
  childLL (childLH (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011211 : AngleCell :=
  childLH (childLH (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011212 : AngleCell :=
  childHL (childLH (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011213 : AngleCell :=
  childHH (childLH (childHL (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011320` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011321` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011322` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011323` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011330` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011331` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011332` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011333` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011300 : AngleCell :=
  childLL (childLL (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011301 : AngleCell :=
  childLH (childLL (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011302 : AngleCell :=
  childHL (childLL (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011303 : AngleCell :=
  childHH (childLL (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011310 : AngleCell :=
  childLL (childLH (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011311 : AngleCell :=
  childLH (childLH (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011312 : AngleCell :=
  childHL (childLH (childHH (childLH thetaBelowCell111133113101)))

/-- Subcell `1111331131011313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111331131011313 : AngleCell :=
  childHH (childLH (childHH (childLH thetaBelowCell111133113101)))

end GerverSofa.PartE.CertificateCells7a1b24c2da

namespace GerverSofa.PartE.CertificateCells3846b81fdf

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022002100)))

end GerverSofa.PartE.CertificateCells3846b81fdf

namespace GerverSofa.PartE.CertificateCells8d8f6e86b1

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells8d8f6e86b1

namespace GerverSofa.PartE.CertificateCells67d4ab08b2

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022002100)))

end GerverSofa.PartE.CertificateCells67d4ab08b2

namespace GerverSofa.PartE.CertificateCells37e4000123

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells37e4000123

namespace GerverSofa.PartE.CertificateCells61d6915992

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells61d6915992

namespace GerverSofa.PartE.CertificateCells49a6e2db55

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells49a6e2db55

namespace GerverSofa.PartE.CertificateCells23cc985c42

/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))

/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))

/-- Subcell `111133113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell111133113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell11113311)))

end GerverSofa.PartE.CertificateCells23cc985c42

namespace GerverSofa.PartE.CoverCertificate19031d0370

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell0000 : AngleCell :=
  childLL cell000

private abbrev cell0001 : AngleCell :=
  childLH cell000

private abbrev cell0002 : AngleCell :=
  childHL cell000

private abbrev cell0003 : AngleCell :=
  childHH cell000

private abbrev cell0010 : AngleCell :=
  childLL cell001

private abbrev cell0011 : AngleCell :=
  childLH cell001

private abbrev cell0012 : AngleCell :=
  childHL cell001

private abbrev cell0013 : AngleCell :=
  childHH cell001

private abbrev cell0100 : AngleCell :=
  childLL cell010

private abbrev cell0101 : AngleCell :=
  childLH cell010

private abbrev cell0102 : AngleCell :=
  childHL cell010

private abbrev cell0103 : AngleCell :=
  childHH cell010

private abbrev cell0110 : AngleCell :=
  childLL cell011

private abbrev cell0111 : AngleCell :=
  childLH cell011

private abbrev cell0112 : AngleCell :=
  childHL cell011

private abbrev cell0113 : AngleCell :=
  childHH cell011

private abbrev cell1000 : AngleCell :=
  childLL cell100

private abbrev cell1001 : AngleCell :=
  childLH cell100

private abbrev cell1002 : AngleCell :=
  childHL cell100

private abbrev cell1003 : AngleCell :=
  childHH cell100

private abbrev cell1010 : AngleCell :=
  childLL cell101

private abbrev cell1011 : AngleCell :=
  childLH cell101

private abbrev cell1012 : AngleCell :=
  childHL cell101

private abbrev cell1013 : AngleCell :=
  childHH cell101

end GerverSofa.PartE.CoverCertificate19031d0370

namespace GerverSofa.PartE.CoverCertificate30936f26ba

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificate30936f26ba

namespace GerverSofa.PartE.CoverCertificate953a140331

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL
    (childHL (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell200 : AngleCell :=
  childLL cell20

private abbrev cell201 : AngleCell :=
  childLH cell20

private abbrev cell202 : AngleCell :=
  childHL cell20

private abbrev cell203 : AngleCell :=
  childHH cell20

private abbrev cell210 : AngleCell :=
  childLL cell21

private abbrev cell211 : AngleCell :=
  childLH cell21

private abbrev cell212 : AngleCell :=
  childHL cell21

private abbrev cell213 : AngleCell :=
  childHH cell21

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell300 : AngleCell :=
  childLL cell30

private abbrev cell301 : AngleCell :=
  childLH cell30

private abbrev cell302 : AngleCell :=
  childHL cell30

private abbrev cell303 : AngleCell :=
  childHH cell30

private abbrev cell310 : AngleCell :=
  childLL cell31

private abbrev cell311 : AngleCell :=
  childLH cell31

private abbrev cell312 : AngleCell :=
  childHL cell31

private abbrev cell313 : AngleCell :=
  childHH cell31

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate953a140331

namespace GerverSofa.PartE.CoverCertificatec0f3040bb9

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL
    (childHL (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell200 : AngleCell :=
  childLL cell20

private abbrev cell201 : AngleCell :=
  childLH cell20

private abbrev cell202 : AngleCell :=
  childHL cell20

private abbrev cell203 : AngleCell :=
  childHH cell20

private abbrev cell210 : AngleCell :=
  childLL cell21

private abbrev cell211 : AngleCell :=
  childLH cell21

private abbrev cell212 : AngleCell :=
  childHL cell21

private abbrev cell213 : AngleCell :=
  childHH cell21

private abbrev cell300 : AngleCell :=
  childLL cell30

private abbrev cell301 : AngleCell :=
  childLH cell30

private abbrev cell302 : AngleCell :=
  childHL cell30

private abbrev cell303 : AngleCell :=
  childHH cell30

private abbrev cell310 : AngleCell :=
  childLL cell31

private abbrev cell311 : AngleCell :=
  childLH cell31

private abbrev cell312 : AngleCell :=
  childHL cell31

private abbrev cell313 : AngleCell :=
  childHH cell31

end GerverSofa.PartE.CoverCertificatec0f3040bb9

namespace GerverSofa.PartE.CoverCertificatec5d26eacb3

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

private abbrev cell2200 : AngleCell :=
  childLL cell220

private abbrev cell2201 : AngleCell :=
  childLH cell220

private abbrev cell2202 : AngleCell :=
  childHL cell220

private abbrev cell2203 : AngleCell :=
  childHH cell220

private abbrev cell2210 : AngleCell :=
  childLL cell221

private abbrev cell2211 : AngleCell :=
  childLH cell221

private abbrev cell2212 : AngleCell :=
  childHL cell221

private abbrev cell2213 : AngleCell :=
  childHH cell221

private abbrev cell2300 : AngleCell :=
  childLL cell230

private abbrev cell2301 : AngleCell :=
  childLH cell230

private abbrev cell2302 : AngleCell :=
  childHL cell230

private abbrev cell2303 : AngleCell :=
  childHH cell230

private abbrev cell2310 : AngleCell :=
  childLL cell231

private abbrev cell2311 : AngleCell :=
  childLH cell231

private abbrev cell2312 : AngleCell :=
  childHL cell231

private abbrev cell2313 : AngleCell :=
  childHH cell231

private abbrev cell3200 : AngleCell :=
  childLL cell320

private abbrev cell3201 : AngleCell :=
  childLH cell320

private abbrev cell3202 : AngleCell :=
  childHL cell320

private abbrev cell3203 : AngleCell :=
  childHH cell320

private abbrev cell3210 : AngleCell :=
  childLL cell321

private abbrev cell3211 : AngleCell :=
  childLH cell321

private abbrev cell3212 : AngleCell :=
  childHL cell321

private abbrev cell3213 : AngleCell :=
  childHH cell321

private abbrev cell3300 : AngleCell :=
  childLL cell330

private abbrev cell3301 : AngleCell :=
  childLH cell330

private abbrev cell3302 : AngleCell :=
  childHL cell330

private abbrev cell3303 : AngleCell :=
  childHH cell330

private abbrev cell3310 : AngleCell :=
  childLL cell331

private abbrev cell3311 : AngleCell :=
  childLH cell331

private abbrev cell3312 : AngleCell :=
  childHL cell331

private abbrev cell3313 : AngleCell :=
  childHH cell331

end GerverSofa.PartE.CoverCertificatec5d26eacb3

namespace GerverSofa.PartE.CoverCertificate3612aa63be

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificate3612aa63be

namespace GerverSofa.PartE.CoverCertificateba32fc9e0a

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificateba32fc9e0a

namespace GerverSofa.PartE.CoverCertificate2170ad4ca0

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate2170ad4ca0

namespace GerverSofa.PartE.CoverCertificate513511aa15

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate513511aa15

namespace GerverSofa.PartE.CoverCertificate3743e2f873

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

private abbrev cell2200 : AngleCell :=
  childLL cell220

private abbrev cell2201 : AngleCell :=
  childLH cell220

private abbrev cell2202 : AngleCell :=
  childHL cell220

private abbrev cell2203 : AngleCell :=
  childHH cell220

private abbrev cell2210 : AngleCell :=
  childLL cell221

private abbrev cell2211 : AngleCell :=
  childLH cell221

private abbrev cell2212 : AngleCell :=
  childHL cell221

private abbrev cell2213 : AngleCell :=
  childHH cell221

private abbrev cell2300 : AngleCell :=
  childLL cell230

private abbrev cell2301 : AngleCell :=
  childLH cell230

private abbrev cell2302 : AngleCell :=
  childHL cell230

private abbrev cell2303 : AngleCell :=
  childHH cell230

end GerverSofa.PartE.CoverCertificate3743e2f873

namespace GerverSofa.PartE.CoverCertificate3e2742ca77

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate3e2742ca77

namespace GerverSofa.PartE.CoverCertificate05d280259b

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificate05d280259b

namespace GerverSofa.PartE.CoverCertificate73ec5d89dc

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificate73ec5d89dc

namespace GerverSofa.PartE.CoverCertificated1fc30835b

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificated1fc30835b

namespace GerverSofa.PartE.CoverCertificatec03bec1842

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatec03bec1842

namespace GerverSofa.PartE.CoverCertificate854ce4fcce

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificate854ce4fcce

namespace GerverSofa.PartE.CoverCertificate756063c6fb

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificate756063c6fb

namespace GerverSofa.PartE.CoverCertificatebb637b4eef

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatebb637b4eef

namespace GerverSofa.PartE.CoverCertificate7fa5919613

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate7fa5919613

namespace GerverSofa.PartE.CoverCertificateb766a036ce

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL
    (childLL (childLL (e24ThetaAboveRoot)))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

end GerverSofa.PartE.CoverCertificateb766a036ce

namespace GerverSofa.PartE.CoverCertificate61295956d2

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLL (childLL
    (childLL (childLL (e24ThetaAboveRoot)))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

end GerverSofa.PartE.CoverCertificate61295956d2

namespace GerverSofa.PartE.CoverCertificate828511f0b8

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL
    (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate828511f0b8

namespace GerverSofa.PartE.CoverCertificated54c339469

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL (childLL
    (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificated54c339469

namespace GerverSofa.PartE.CoverCertificate4dd8dcfac0

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate4dd8dcfac0

namespace GerverSofa.PartE.CoverCertificate4ee27c37fd

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate4ee27c37fd

namespace GerverSofa.PartE.CoverCertificated7b655454c

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificated7b655454c

namespace GerverSofa.PartE.CoverCertificate34bc1a6525

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificate34bc1a6525

namespace GerverSofa.PartE.CoverCertificate6e40ca0512

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate6e40ca0512

namespace GerverSofa.PartE.CoverCertificateefd035cf65

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificateefd035cf65

namespace GerverSofa.PartE.CoverCertificatea4b667aaa0

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificatea4b667aaa0

namespace GerverSofa.PartE.CoverCertificateccad0dc048

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificateccad0dc048

namespace GerverSofa.PartE.CoverCertificate89deca0334

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate89deca0334

namespace GerverSofa.PartE.CoverCertificate8778f820bd

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate8778f820bd

namespace GerverSofa.PartE.CoverCertificatef14d24461a

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificatef14d24461a

namespace GerverSofa.PartE.CoverCertificate79980b2e6c

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate79980b2e6c

namespace GerverSofa.PartE.CoverCertificateed2ff1f24e

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificateed2ff1f24e

namespace GerverSofa.PartE.CoverCertificate4bcf50db3e

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate4bcf50db3e

namespace GerverSofa.PartE.CoverCertificate1e4788169b

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate1e4788169b

namespace GerverSofa.PartE.CoverCertificate4f5a63a5df

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

end GerverSofa.PartE.CoverCertificate4f5a63a5df

namespace GerverSofa.PartE.CoverCertificate89bb9fd21e

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate89bb9fd21e

namespace GerverSofa.PartE.CoverCertificate5c80136736

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL
    (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate5c80136736

namespace GerverSofa.PartE.CoverCertificate645f79320a

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate645f79320a

namespace GerverSofa.PartE.CoverCertificate3e0a4a2c6f

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childLL (childLH (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3e0a4a2c6f

namespace GerverSofa.PartE.CertificateCells6deb17ad88

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells6deb17ad88

namespace GerverSofa.PartE.CertificateCells21b7c7dcb8

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells21b7c7dcb8

namespace GerverSofa.PartE.CertificateCells51629e8703

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCells51629e8703

namespace GerverSofa.PartE.CertificateCellse4c4271ea3

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCellse4c4271ea3

namespace GerverSofa.PartE.CertificateCells07d8bdd7d9

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCells07d8bdd7d9

namespace GerverSofa.PartE.CertificateCells2bf9eb5708

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCells2bf9eb5708

namespace GerverSofa.PartE.CertificateCells7eefa0b856

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells7eefa0b856

namespace GerverSofa.PartE.CertificateCellsdb6ef42c13

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsdb6ef42c13

namespace GerverSofa.PartE.CertificateCells91885e0374

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells91885e0374

namespace GerverSofa.PartE.CertificateCellsba71b1d520

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsba71b1d520

namespace GerverSofa.PartE.CertificateCells54caf0dec0

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells54caf0dec0

namespace GerverSofa.PartE.CertificateCells22ecf07105

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells22ecf07105

namespace GerverSofa.PartE.CertificateCells2d236bc977

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells2d236bc977

namespace GerverSofa.PartE.CertificateCellsfbf08c6815

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsfbf08c6815

namespace GerverSofa.PartE.CertificateCellsb2588049db

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsb2588049db

namespace GerverSofa.PartE.CertificateCells80702a4342

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells80702a4342

namespace GerverSofa.PartE.CertificateCellsfcacd99e70

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsfcacd99e70

namespace GerverSofa.PartE.CertificateCellsc63c49e043

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsc63c49e043

namespace GerverSofa.PartE.CertificateCellse2c2881509

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellse2c2881509

namespace GerverSofa.PartE.CertificateCells1273bfc545

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells1273bfc545

namespace GerverSofa.PartE.CertificateCells758d72a450

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells758d72a450

namespace GerverSofa.PartE.CertificateCells898eeb07c6

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells898eeb07c6

namespace GerverSofa.PartE.CertificateCells3b9ec898a9

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells3b9ec898a9

namespace GerverSofa.PartE.CertificateCellscbef0a66a7

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellscbef0a66a7

namespace GerverSofa.PartE.CertificateCells0e30799078

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells0e30799078

namespace GerverSofa.PartE.CertificateCellsaa7ab31314

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsaa7ab31314

namespace GerverSofa.PartE.CertificateCellsa4a7cbe7b2

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsa4a7cbe7b2

namespace GerverSofa.PartE.CertificateCells9f358cc74d

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells9f358cc74d

namespace GerverSofa.PartE.CertificateCellsf2bd9cd8f9

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsf2bd9cd8f9

namespace GerverSofa.PartE.CertificateCellse30fe464b6

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellse30fe464b6

namespace GerverSofa.PartE.CertificateCells50e57ae8a7

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells50e57ae8a7

namespace GerverSofa.PartE.CertificateCells6831b5295c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells6831b5295c

namespace GerverSofa.PartE.CertificateCells6ec7ee0b32

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells6ec7ee0b32

namespace GerverSofa.PartE.CertificateCellscdb025ab65

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellscdb025ab65

namespace GerverSofa.PartE.CertificateCells251eb00cd5

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells251eb00cd5

namespace GerverSofa.PartE.CertificateCellsb46fd93863

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsb46fd93863

namespace GerverSofa.PartE.CertificateCells02c02b7fd3

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells02c02b7fd3

namespace GerverSofa.PartE.CertificateCells969e2199d5

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells969e2199d5

namespace GerverSofa.PartE.CertificateCells99f6185557

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells99f6185557

namespace GerverSofa.PartE.CertificateCellsea3eb05dc6

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsea3eb05dc6

namespace GerverSofa.PartE.CertificateCells1daa3566d0

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells1daa3566d0

namespace GerverSofa.PartE.CertificateCells04b8a575e1

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells04b8a575e1

namespace GerverSofa.PartE.CertificateCellsb52fa9450d

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsb52fa9450d

namespace GerverSofa.PartE.CertificateCells75262755f1

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells75262755f1

namespace GerverSofa.PartE.CertificateCells88775d9be2

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells88775d9be2

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6R4Subtree7c075da8e9f0577b`.
* `KernelOnly.PartE.E24KC6R4Subtree7e83efce8bd8caa9`.
* `KernelOnly.PartE.E24KC6R4Join57ced70670a400e2`.
* `KernelOnly.PartE.E24KC6R4Subtree81ebe3f900bc76a5`.
* `KernelOnly.PartE.E24KC6R4Subtree84bebec26b36007b`.
* `KernelOnly.PartE.E24KC6R4Subtree879f3ccc81ca9b24`.
* `KernelOnly.PartE.E24KC6R4Subtree88f80fd4db374a2d`.
* `KernelOnly.PartE.E24KC6R4Subtree8921da6a3153d018`.
* `KernelOnly.PartE.E24KC6R4Subtree89badd31312e459d`.
* `KernelOnly.PartE.E24KC6R4Subtree8b6172e52c41dded`.
* `KernelOnly.PartE.E24KC6R4Join0f0434a94ae699a2`.
-/

public section

noncomputable section

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsefec3b1324

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsefec3b1324

open CertificateCellsefec3b1324
theorem cover_subtree_7aa3d52e724a :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111222 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111222
    (by
      have h : ((childLL thetaBelowCell1111331131111222)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111222) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111222)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111222) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111222)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111222)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111222)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111222)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111222))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111222)) h))

theorem cover_subtree_818c6b64504a :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111223 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111223
    (by
      have h : ((childLL thetaBelowCell1111331131111223)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111223) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111223)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111223) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111223)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111223)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111223)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111223)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111223))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111223)) h))

theorem cover_subtree_75546d36bae0 :
    adaptiveCoverCheck 3 (childHL (childHL (childLH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH
    thetaBelowCell111133113111)))
    (by
      have h : (thetaBelowCell1111331131111220).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111220 h)
    (by
      have h : (thetaBelowCell1111331131111221).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111221 h)
    cover_subtree_7aa3d52e724a
    cover_subtree_818c6b64504a

theorem cover_subtree_38aeeec8d754 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111232 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111232
    (by
      have h : ((childLL thetaBelowCell1111331131111232)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111232) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111232)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111232) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111232)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111232)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111232)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111232)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111232))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111232)) h))

theorem cover_subtree_7653e3da7d41 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111233 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111233
    (by
      have h : ((childLL thetaBelowCell1111331131111233)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111233) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111233)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111233) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111233)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111233)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111233)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111233)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111233))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111233)) h))

theorem cover_subtree_c48c3d0e1082 :
    adaptiveCoverCheck 3 (childHH (childHL (childLH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH
    thetaBelowCell111133113111)))
    (by
      have h : (thetaBelowCell1111331131111230).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111230 h)
    (by
      have h : (thetaBelowCell1111331131111231).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111231 h)
    cover_subtree_38aeeec8d754
    cover_subtree_7653e3da7d41

theorem cover_subtree_850575b22b27 :
    adaptiveCoverCheck 4 (childHL (childLH thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHL (childLH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childLH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHL (childLH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childLH
        thetaBelowCell111133113111))) h)
    cover_subtree_75546d36bae0
    cover_subtree_c48c3d0e1082

theorem cover_subtree_8b97f2fa7857 :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111322 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111322
    (by
      have h : ((childLL thetaBelowCell1111331131111322)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111322) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111322)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111322) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111322)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111322)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111322)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111322)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111322))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111322)) h))

theorem cover_subtree_4e37d42ba06c :
    adaptiveCoverCheck 2 thetaBelowCell1111331131111323 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111323
    (by
      have h : ((childLL thetaBelowCell1111331131111323)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111323) h)
    (by
      have h : ((childLH thetaBelowCell1111331131111323)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111323) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHL thetaBelowCell1111331131111323)
        (by
          have h : ((childLL (childHL thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHL
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childLH (childHL thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHL
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childHL (childHL thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHL
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childHH (childHL thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHL
            thetaBelowCell1111331131111323)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 0 (childHH thetaBelowCell1111331131111323)
        (by
          have h : ((childLL (childHH thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLL (childHH
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childLH (childHH thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childLH (childHH
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childHL (childHH thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHL (childHH
            thetaBelowCell1111331131111323)) h)
        (by
          have h : ((childHH (childHH thetaBelowCell1111331131111323))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 0 (childHH (childHH
            thetaBelowCell1111331131111323)) h))

theorem cover_subtree_27a9e6ae3bf9 :
    adaptiveCoverCheck 3 (childHL (childHH (childLH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH
    thetaBelowCell111133113111)))
    (by
      have h : (thetaBelowCell1111331131111320).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111320 h)
    (by
      have h : (thetaBelowCell1111331131111321).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111321 h)
    cover_subtree_8b97f2fa7857
    cover_subtree_4e37d42ba06c

theorem cover_subtree_73b432883d7f :
    adaptiveCoverCheck 3 (childHH (childHH (childLH thetaBelowCell111133113111))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH
    thetaBelowCell111133113111)))
    (by
      have h : (thetaBelowCell1111331131111330).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111330 h)
    (by
      have h : (thetaBelowCell1111331131111331).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131111331 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111332
        (by
          have h : ((childLL thetaBelowCell1111331131111332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111332) h)
        (by
          have h : ((childLH thetaBelowCell1111331131111332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111332) h)
        (by
          have h : ((childHL thetaBelowCell1111331131111332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131111332) h)
        (by
          have h : ((childHH thetaBelowCell1111331131111332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131111332) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131111333
        (by
          have h : ((childLL thetaBelowCell1111331131111333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131111333) h)
        (by
          have h : ((childLH thetaBelowCell1111331131111333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131111333) h)
        (by
          have h : ((childHL thetaBelowCell1111331131111333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131111333) h)
        (by
          have h : ((childHH thetaBelowCell1111331131111333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131111333) h))

theorem cover_subtree_cff1fffcbf04 :
    adaptiveCoverCheck 4 (childHH (childLH thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHH (childLH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childLH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHH (childLH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childLH
        thetaBelowCell111133113111))) h)
    cover_subtree_27a9e6ae3bf9
    cover_subtree_73b432883d7f

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c1 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113111) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113111)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113111))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133113111))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133113111))) h))
    (by
      have h : ((childLH (childLH thetaBelowCell111133113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH thetaBelowCell111133113111)) h)
    cover_subtree_850575b22b27
    cover_subtree_cff1fffcbf04

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

namespace CertificateCells11cd3db1c7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells11cd3db1c7

open CertificateCells11cd3db1c7
theorem cover_subtree_36a7bfb19453 :
    adaptiveCoverCheck 3 (childLL (childLL (childHH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLL (childHH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103000
        (by
          have h : ((childLL thetaBelowCell1111331131103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103000) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103000) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103000) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103001
        (by
          have h : ((childLL thetaBelowCell1111331131103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103001) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103001) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103001) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103001) h))
    (by
      have h : (thetaBelowCell1111331131103002).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103002 h)
    (by
      have h : (thetaBelowCell1111331131103003).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103003 h)

theorem cover_subtree_05a08e0bea5f :
    adaptiveCoverCheck 3 (childLH (childLL (childHH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLL (childHH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103010
        (by
          have h : ((childLL thetaBelowCell1111331131103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103010) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103010) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103010) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103011
        (by
          have h : ((childLL thetaBelowCell1111331131103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103011) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103011) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103011) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103011) h))
    (by
      have h : (thetaBelowCell1111331131103012).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103012 h)
    (by
      have h : (thetaBelowCell1111331131103013).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103013 h)

theorem cover_subtree_e2abbc5cba3c :
    adaptiveCoverCheck 4 (childLL (childHH thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH thetaBelowCell111133113110))
    cover_subtree_36a7bfb19453
    cover_subtree_05a08e0bea5f
    (by
      have h : ((childHL (childLL (childHH thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childHH
        thetaBelowCell111133113110))) h)
    (by
      have h : ((childHH (childLL (childHH thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childHH
        thetaBelowCell111133113110))) h)

theorem cover_subtree_09ec3c616243 :
    adaptiveCoverCheck 3 (childLL (childLH (childHH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLL (childLH (childHH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103100
        (by
          have h : ((childLL thetaBelowCell1111331131103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103100) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103100) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103100) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103101
        (by
          have h : ((childLL thetaBelowCell1111331131103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103101) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103101) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103101) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103101) h))
    (by
      have h : (thetaBelowCell1111331131103102).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103102 h)
    (by
      have h : (thetaBelowCell1111331131103103).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103103 h)

theorem cover_subtree_6c69a3f38b7c :
    adaptiveCoverCheck 3 (childLH (childLH (childHH thetaBelowCell111133113110))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childLH (childLH (childHH
    thetaBelowCell111133113110)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103110
        (by
          have h : ((childLL thetaBelowCell1111331131103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103110) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103110) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103110) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131103111
        (by
          have h : ((childLL thetaBelowCell1111331131103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131103111) h)
        (by
          have h : ((childLH thetaBelowCell1111331131103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131103111) h)
        (by
          have h : ((childHL thetaBelowCell1111331131103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131103111) h)
        (by
          have h : ((childHH thetaBelowCell1111331131103111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131103111) h))
    (by
      have h : (thetaBelowCell1111331131103112).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103112 h)
    (by
      have h : (thetaBelowCell1111331131103113).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103113 h)

theorem cover_subtree_5b1de072a154 :
    adaptiveCoverCheck 4 (childLH (childHH thetaBelowCell111133113110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH thetaBelowCell111133113110))
    cover_subtree_09ec3c616243
    cover_subtree_6c69a3f38b7c
    (by
      have h : ((childHL (childLH (childHH thetaBelowCell111133113110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childHH
        thetaBelowCell111133113110))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childHH (childLH (childHH
        thetaBelowCell111133113110)))
        (by
          have h : (thetaBelowCell1111331131103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103130 h)
        (by
          have h : (thetaBelowCell1111331131103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103131 h)
        (by
          have h : (thetaBelowCell1111331131103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103132 h)
        (by
          have h : (thetaBelowCell1111331131103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131103133 h))

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c3 :
    adaptiveCoverCheck 5 (childHH thetaBelowCell111133113110) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH thetaBelowCell111133113110)
    cover_subtree_e2abbc5cba3c
    cover_subtree_5b1de072a154
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133113110))
        (by
          have h : ((childLL (childHL (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
            thetaBelowCell111133113110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHH thetaBelowCell111133113110))
        (by
          have h : ((childLL (childHH (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHH
            thetaBelowCell111133113110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaBelowCell111133113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHH
            thetaBelowCell111133113110))) h))

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

namespace CertificateCellse82c2dced4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse82c2dced4

open CertificateCellse82c2dced4

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c0 :
    adaptiveCoverCheck 6 thetaBelowCell111133113110 = true :=
  adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113110
    e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c0 e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c1
      e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c2 e24KC2ThetaBelowLeaf111133113_c1_c1_c0_c3

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

namespace CertificateCells7a1b24c2da

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells7a1b24c2da

open CertificateCells7a1b24c2da
theorem cover_subtree_9615f1192754 :
    adaptiveCoverCheck 3 (childHL (childHL (childLH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHL (childLH
    thetaBelowCell111133113101)))
    (by
      have h : (thetaBelowCell1111331131011220).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011220 h)
    (by
      have h : (thetaBelowCell1111331131011221).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011221 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011222
        (by
          have h : ((childLL thetaBelowCell1111331131011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011222) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011222) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011222) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011222)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011222) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011223
        (by
          have h : ((childLL thetaBelowCell1111331131011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011223) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011223) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011223) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011223)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011223) h))

theorem cover_subtree_1f726b3116b0 :
    adaptiveCoverCheck 3 (childHH (childHL (childLH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHL (childLH
    thetaBelowCell111133113101)))
    (by
      have h : (thetaBelowCell1111331131011230).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011230 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011231
        (by
          have h : ((childLL thetaBelowCell1111331131011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011231) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011231) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011231) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011231)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011231) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011232
        (by
          have h : ((childLL thetaBelowCell1111331131011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011232) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011232) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011232) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011232)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011232) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011233
        (by
          have h : ((childLL thetaBelowCell1111331131011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011233) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011233) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011233) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011233)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011233) h))

theorem cover_subtree_cac2e3b1401d :
    adaptiveCoverCheck 4 (childHL (childLH thetaBelowCell111133113101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH thetaBelowCell111133113101))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHL (childLH
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131011200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011200 h)
        (by
          have h : (thetaBelowCell1111331131011201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011201 h)
        (by
          have h : (thetaBelowCell1111331131011202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011202 h)
        (by
          have h : (thetaBelowCell1111331131011203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHL (childLH
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131011210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011210 h)
        (by
          have h : (thetaBelowCell1111331131011211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011211 h)
        (by
          have h : (thetaBelowCell1111331131011212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011212 h)
        (by
          have h : (thetaBelowCell1111331131011213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011213 h))
    cover_subtree_9615f1192754
    cover_subtree_1f726b3116b0

theorem cover_subtree_4f3cdd0c257d :
    adaptiveCoverCheck 3 (childHL (childHH (childLH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHL (childHH (childLH
    thetaBelowCell111133113101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011320
        (by
          have h : ((childLL thetaBelowCell1111331131011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011320) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011320) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011320) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011320)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011320) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011321
        (by
          have h : ((childLL thetaBelowCell1111331131011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011321) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011321) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011321) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011321)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011321) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011322
        (by
          have h : ((childLL thetaBelowCell1111331131011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011322) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011322) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011322) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011322)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011322) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011323
        (by
          have h : ((childLL thetaBelowCell1111331131011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011323) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011323) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011323) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011323)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011323) h))

theorem cover_subtree_8b305093aef1 :
    adaptiveCoverCheck 3 (childHH (childHH (childLH thetaBelowCell111133113101))) = true := by
  exact adaptiveCoverCheck_succ_of_children 2 (childHH (childHH (childLH
    thetaBelowCell111133113101)))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011330
        (by
          have h : ((childLL thetaBelowCell1111331131011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011330) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011330) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011330) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011330)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011330) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011331
        (by
          have h : ((childLL thetaBelowCell1111331131011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011331) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011331) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011331) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011331)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011331) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011332
        (by
          have h : ((childLL thetaBelowCell1111331131011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011332) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011332) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011332) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011332)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011332) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011333
        (by
          have h : ((childLL thetaBelowCell1111331131011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011333) h)
        (by
          have h : ((childLH thetaBelowCell1111331131011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011333) h)
        (by
          have h : ((childHL thetaBelowCell1111331131011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011333) h)
        (by
          have h : ((childHH thetaBelowCell1111331131011333)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011333) h))

theorem cover_subtree_38619e7e6aac :
    adaptiveCoverCheck 4 (childHH (childLH thetaBelowCell111133113101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH thetaBelowCell111133113101))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLL (childHH (childLH
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131011300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011300 h)
        (by
          have h : (thetaBelowCell1111331131011301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011301 h)
        (by
          have h : (thetaBelowCell1111331131011302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011302 h)
        (by
          have h : (thetaBelowCell1111331131011303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 (childLH (childHH (childLH
        thetaBelowCell111133113101)))
        (by
          have h : (thetaBelowCell1111331131011310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011310 h)
        (by
          have h : (thetaBelowCell1111331131011311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011311 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 1 thetaBelowCell1111331131011312
            (by
              have h : ((childLL thetaBelowCell1111331131011312)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLL thetaBelowCell1111331131011312)
                h)
            (by
              have h : ((childLH thetaBelowCell1111331131011312)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childLH thetaBelowCell1111331131011312)
                h)
            (by
              have h : ((childHL thetaBelowCell1111331131011312)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHL thetaBelowCell1111331131011312)
                h)
            (by
              have h : ((childHH thetaBelowCell1111331131011312)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 1 (childHH thetaBelowCell1111331131011312)
                h))
        (by
          have h : (thetaBelowCell1111331131011313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 thetaBelowCell1111331131011313 h))
    cover_subtree_4f3cdd0c257d
    cover_subtree_8b305093aef1

theorem e24KC2ThetaBelowLeaf111133113_c1_c0_c1_c1 :
    adaptiveCoverCheck 5 (childLH thetaBelowCell111133113101) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113101)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLH thetaBelowCell111133113101))
        (by
          have h : ((childLL (childLL (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLL (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childLH (childLL (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLL (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHL (childLL (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLL (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHH (childLL (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLL (childLH
            thetaBelowCell111133113101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLH thetaBelowCell111133113101))
        (by
          have h : ((childLL (childLH (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childLH (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childLH (childLH (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childLH (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHL (childLH (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childLH (childLH
            thetaBelowCell111133113101))) h)
        (by
          have h : ((childHH (childLH (childLH thetaBelowCell111133113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childLH (childLH
            thetaBelowCell111133113101))) h))
    cover_subtree_cac2e3b1401d
    cover_subtree_38619e7e6aac

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

namespace CertificateCells3846b81fdf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3846b81fdf

open CertificateCells3846b81fdf
theorem cover_subtree_c9cdbb673d76 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003002 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003002
    (by
      have h : ((childLL thetaAboveCell0000220021003002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003002) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003002) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003002)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003002)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003002)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003002)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003002))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003002)) h))

theorem cover_subtree_0d25773c4d7a :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003003 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003003
    (by
      have h : ((childLL thetaAboveCell0000220021003003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003003) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003003) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003003)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003003)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003003)) h))

theorem cover_subtree_d91230c1595a :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLL (childLL (childHH
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021003000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003000 h)
    (by
      have h : (thetaAboveCell0000220021003001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003001 h)
    cover_subtree_c9cdbb673d76
    cover_subtree_0d25773c4d7a

theorem cover_subtree_3b00f6acc230 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003012 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003012
    (by
      have h : ((childLL thetaAboveCell0000220021003012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003012) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003012) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003012)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003012)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003012)) h))

theorem cover_subtree_7ad163274380 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003013 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003013
    (by
      have h : ((childLL thetaAboveCell0000220021003013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003013) h)
    (by
      have h : ((childLH thetaAboveCell0000220021003013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003013) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003013)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003013)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003013)) h))

theorem cover_subtree_5685dda3095f :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childLH (childLL (childHH
    thetaAboveCell000022002100)))
    (by
      have h : (thetaAboveCell0000220021003010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003010 h)
    (by
      have h : (thetaAboveCell0000220021003011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003011 h)
    cover_subtree_3b00f6acc230
    cover_subtree_7ad163274380

theorem cover_subtree_f7f8133fac9a :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003020 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003020
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003020)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003020)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003020)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003020)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003020)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003020)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003020))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003020)) h))

theorem cover_subtree_34eb89665f6e :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003021 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003021
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003021)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003021)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003021)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003021)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003021)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003021)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003021))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003021)) h))

theorem cover_subtree_854759339591 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
    thetaAboveCell000022002100)))
    cover_subtree_f7f8133fac9a
    cover_subtree_34eb89665f6e
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003022
        (by
          have h : ((childLL thetaAboveCell0000220021003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003022) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003022) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003022) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003023
        (by
          have h : ((childLL thetaAboveCell0000220021003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003023) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003023) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003023) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003023) h))

theorem cover_subtree_a49deaaa8f12 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003030 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003030
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003030)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003030)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003030)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003030)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003030)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003030)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003030))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003030)) h))

theorem cover_subtree_2236023309b5 :
    adaptiveCoverCheck 3 thetaAboveCell0000220021003031 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003031
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLL thetaAboveCell0000220021003031)
        (by
          have h : ((childLL (childLL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLL
            thetaAboveCell0000220021003031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childLH thetaAboveCell0000220021003031)
        (by
          have h : ((childLL (childLH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childLH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childLH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childLH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childLH
            thetaAboveCell0000220021003031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHL thetaAboveCell0000220021003031)
        (by
          have h : ((childLL (childHL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHL
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHL
            thetaAboveCell0000220021003031)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 1 (childHH thetaAboveCell0000220021003031)
        (by
          have h : ((childLL (childHH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLL (childHH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childLH (childHH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHL (childHH
            thetaAboveCell0000220021003031)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell0000220021003031))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 1 (childHH (childHH
            thetaAboveCell0000220021003031)) h))

theorem cover_subtree_2c168101607b :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002100))) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
    thetaAboveCell000022002100)))
    cover_subtree_a49deaaa8f12
    cover_subtree_2236023309b5
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003032
        (by
          have h : ((childLL thetaAboveCell0000220021003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003032) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003032) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003032) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 2 thetaAboveCell0000220021003033
        (by
          have h : ((childLL thetaAboveCell0000220021003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLL thetaAboveCell0000220021003033) h)
        (by
          have h : ((childLH thetaAboveCell0000220021003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childLH thetaAboveCell0000220021003033) h)
        (by
          have h : ((childHL thetaAboveCell0000220021003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHL thetaAboveCell0000220021003033) h)
        (by
          have h : ((childHH thetaAboveCell0000220021003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 2 (childHH thetaAboveCell0000220021003033) h))

theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c0 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022002100))
    cover_subtree_d91230c1595a
    cover_subtree_5685dda3095f
    cover_subtree_854759339591
    cover_subtree_2c168101607b

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

namespace CertificateCells8d8f6e86b1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells8d8f6e86b1

open CertificateCells8d8f6e86b1
theorem e24KC2ThetaAboveLeaf0000220021_c1_c2 :
    adaptiveCoverCheck 7 thetaAboveCell000022002112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022002112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022002112)
        (by
          have h : ((childLL (childLL thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022002112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022002112)
        (by
          have h : ((childLL (childLH thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022002112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022002112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022002112)) h))
    (by
      have h : ((childHL thetaAboveCell000022002112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022002112) h)
    (by
      have h : ((childHH thetaAboveCell000022002112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022002112) h)

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

namespace CertificateCells67d4ab08b2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells67d4ab08b2

open CertificateCells67d4ab08b2
theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022002100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003200 h)
        (by
          have h : (thetaAboveCell0000220021003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003201 h)
        (by
          have h : (thetaAboveCell0000220021003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003202 h)
        (by
          have h : (thetaAboveCell0000220021003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003210 h)
        (by
          have h : (thetaAboveCell0000220021003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003211 h)
        (by
          have h : (thetaAboveCell0000220021003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003212 h)
        (by
          have h : (thetaAboveCell0000220021003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022002100))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
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

namespace CertificateCells37e4000123

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells37e4000123

open CertificateCells37e4000123
theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c3 :
    adaptiveCoverCheck 6 thetaBelowCell111133113113 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 thetaBelowCell111133113113
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL thetaBelowCell111133113113)
        (by
          have h : ((childLL (childLL thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childLH (childLL thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childHL (childLL thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childHH (childLL thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL
            thetaBelowCell111133113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH thetaBelowCell111133113113)
        (by
          have h : ((childLL (childLH thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childLH (childLH thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childHL (childLH thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH
            thetaBelowCell111133113113)) h)
        (by
          have h : ((childHH (childLH thetaBelowCell111133113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH
            thetaBelowCell111133113113)) h))
    (by
      have h : ((childHL thetaBelowCell111133113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL thetaBelowCell111133113113) h)
    (by
      have h : ((childHH thetaBelowCell111133113113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH thetaBelowCell111133113113) h)

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

namespace CertificateCells61d6915992

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells61d6915992

open CertificateCells61d6915992
theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c3_c2 :
    adaptiveCoverCheck 4 (childHL (childHH thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHL (childHH thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHL (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHL (childHH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHL (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHL (childHH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHL (childHL (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHL (childHH
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHH (childHL (childHH thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHL (childHH
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

namespace CertificateCells49a6e2db55

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells49a6e2db55

open CertificateCells49a6e2db55
theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c3 :
    adaptiveCoverCheck 4 (childHH (childHL thetaBelowCell111133113111)) = true := by
  exact adaptiveCoverCheck_succ_of_children 3 (childHH (childHL thetaBelowCell111133113111))
    (by
      have h : ((childLL (childHH (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLL (childHH (childHL
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childLH (childHH (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childLH (childHH (childHL
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHL (childHH (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHL (childHH (childHL
        thetaBelowCell111133113111))) h)
    (by
      have h : ((childHH (childHH (childHL thetaBelowCell111133113111)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 3 (childHH (childHH (childHL
        thetaBelowCell111133113111))) h)

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

namespace CertificateCells23cc985c42

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells23cc985c42

open CertificateCells23cc985c42

theorem e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2 :
    adaptiveCoverCheck 5 (childHL thetaBelowCell111133113111) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childHL thetaBelowCell111133113111)
    e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c0 e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c1
      e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c2 e24KC2ThetaBelowLeaf111133113_c1_c1_c1_c2_c3

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

* `KernelOnly.PartE.ThetaAbove.Leaf00567`.
* `KernelOnly.PartE.ThetaAbove.Leaf00568`.
* `KernelOnly.PartE.ThetaAbove.Leaf00572`.
* `KernelOnly.PartE.ThetaAbove.Leaf00573`.
* `KernelOnly.PartE.ThetaAbove.Leaf00574`.
* `KernelOnly.PartE.ThetaAbove.Leaf00575`.
* `KernelOnly.PartE.ThetaAbove.Leaf00577`.
* `KernelOnly.PartE.ThetaAbove.Leaf00578`.
* `KernelOnly.PartE.ThetaAbove.Leaf00579`.
* `KernelOnly.PartE.ThetaAbove.Leaf00581`.
* `KernelOnly.PartE.ThetaAbove.Leaf00582`.
* `KernelOnly.PartE.ThetaAbove.Leaf00586`.
* `KernelOnly.PartE.ThetaAbove.Leaf00587`.
* `KernelOnly.PartE.ThetaAbove.Leaf00588`.
* `KernelOnly.PartE.ThetaAbove.Leaf00589`.
* `KernelOnly.PartE.ThetaAbove.Leaf00592`.
* `KernelOnly.PartE.ThetaAbove.Leaf00593`.
* `KernelOnly.PartE.ThetaAbove.Leaf00594`.
* `KernelOnly.PartE.ThetaAbove.Leaf00595`.
* `KernelOnly.PartE.ThetaAbove.Leaf00597`.
* `KernelOnly.PartE.ThetaAbove.Leaf00598`.
* `KernelOnly.PartE.ThetaAbove.Leaf00601`.
* `KernelOnly.PartE.ThetaAbove.Leaf00602`.
* `KernelOnly.PartE.ThetaAbove.Leaf00606`.
* `KernelOnly.PartE.ThetaAbove.Leaf00607`.
* `KernelOnly.PartE.ThetaAbove.Leaf00610`.
* `KernelOnly.PartE.ThetaAbove.Leaf00611`.
* `KernelOnly.PartE.ThetaAbove.Leaf00612`.
* `KernelOnly.PartE.ThetaAbove.Leaf00613`.
* `KernelOnly.PartE.ThetaAbove.Leaf00616`.
* `KernelOnly.PartE.ThetaAbove.Leaf00617`.
* `KernelOnly.PartE.ThetaAbove.Leaf00618`.
* `KernelOnly.PartE.ThetaAbove.Leaf00619`.
* `KernelOnly.PartE.ThetaAbove.Leaf00621`.
* `KernelOnly.PartE.ThetaAbove.Leaf00622`.
* `KernelOnly.PartE.ThetaAbove.Leaf00626`.
* `KernelOnly.PartE.ThetaAbove.Leaf00627`.
* `KernelOnly.PartE.ThetaAbove.Leaf00628`.
* `KernelOnly.PartE.ThetaAbove.Leaf00629`.
* `KernelOnly.PartE.ThetaAbove.Leaf00632`.
* `KernelOnly.PartE.ThetaAbove.Leaf00633`.
* `KernelOnly.PartE.ThetaAbove.Leaf00634`.
* `KernelOnly.PartE.ThetaAbove.Leaf00635`.
* `KernelOnly.PartE.ThetaAbove.Leaf00637`.
* `KernelOnly.PartE.ThetaAbove.Leaf00638`.
-/

public section

noncomputable section

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c2_4_00567
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6deb17ad88

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6deb17ad88

open CertificateCells6deb17ad88
namespace CoverCertificate19031d0370

private theorem checked0000 : adaptiveCoverCheck 0 cell0000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0000 (by decide +kernel)

private theorem checked0001 : adaptiveCoverCheck 0 cell0001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0001 (by decide +kernel)

private theorem checked0002 : adaptiveCoverCheck 0 cell0002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0002 (by decide +kernel)

private theorem checked0003 : adaptiveCoverCheck 0 cell0003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0003 (by decide +kernel)

private theorem checked0010 : adaptiveCoverCheck 0 cell0010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0010 (by decide +kernel)

private theorem checked0011 : adaptiveCoverCheck 0 cell0011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0011 (by decide +kernel)

private theorem checked0012 : adaptiveCoverCheck 0 cell0012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0012 (by decide +kernel)

private theorem checked0013 : adaptiveCoverCheck 0 cell0013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0013 (by decide +kernel)

private theorem checked0100 : adaptiveCoverCheck 0 cell0100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0100 (by decide +kernel)

private theorem checked0101 : adaptiveCoverCheck 0 cell0101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0101 (by decide +kernel)

private theorem checked0102 : adaptiveCoverCheck 0 cell0102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0102 (by decide +kernel)

private theorem checked0103 : adaptiveCoverCheck 0 cell0103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0103 (by decide +kernel)

private theorem checked0110 : adaptiveCoverCheck 0 cell0110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0110 (by decide +kernel)

private theorem checked0111 : adaptiveCoverCheck 0 cell0111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0111 (by decide +kernel)

private theorem checked0112 : adaptiveCoverCheck 0 cell0112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0112 (by decide +kernel)

private theorem checked0113 : adaptiveCoverCheck 0 cell0113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0113 (by decide +kernel)

private theorem checked1000 : adaptiveCoverCheck 0 cell1000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1000 (by decide +kernel)

private theorem checked1001 : adaptiveCoverCheck 0 cell1001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1001 (by decide +kernel)

private theorem checked1002 : adaptiveCoverCheck 0 cell1002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1002 (by decide +kernel)

private theorem checked1003 : adaptiveCoverCheck 0 cell1003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1003 (by decide +kernel)

private theorem checked1010 : adaptiveCoverCheck 0 cell1010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1010 (by decide +kernel)

private theorem checked1011 : adaptiveCoverCheck 0 cell1011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1011 (by decide +kernel)

private theorem checked1012 : adaptiveCoverCheck 0 cell1012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1012 (by decide +kernel)

private theorem checked1013 : adaptiveCoverCheck 0 cell1013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1013 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell000
    checked0000 checked0001 checked0002 checked0003

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell001
    checked0010 checked0011 checked0012 checked0013

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell010
    checked0100 checked0101 checked0102 checked0103

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell011
    checked0110 checked0111 checked0112 checked0113

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell100
    checked1000 checked1001 checked1002 checked1003

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell101
    checked1010 checked1011 checked1012 checked1013

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate19031d0370

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificate19031d0370.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c3_4_00568
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells21b7c7dcb8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells21b7c7dcb8

open CertificateCells21b7c7dcb8
namespace CoverCertificate30936f26ba

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate30936f26ba

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificate30936f26ba.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_c0_3_00572
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells51629e8703

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells51629e8703

open CertificateCells51629e8703
theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012100 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_c1_3_00573
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse4c4271ea3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse4c4271ea3

open CertificateCellse4c4271ea3
theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012101 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_c2_3_00574
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells07d8bdd7d9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells07d8bdd7d9

open CertificateCells07d8bdd7d9
namespace CoverCertificate953a140331

private theorem checked200 : adaptiveCoverCheck 0 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 0 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 0 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 0 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 0 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 0 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 0 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 0 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell213 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 0 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 0 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 0 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 0 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 0 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 0 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 0 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 0 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell233 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 0 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 0 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 0 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 0 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 0 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 0 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 0 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 0 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 0 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 0 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 0 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 0 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 0 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 0 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 0 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 0 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 1 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 1 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 1 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 1 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate953a140331

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012102 = true := by
  exact CoverCertificate953a140331.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c0_c3_3_00575
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2bf9eb5708

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2bf9eb5708

open CertificateCells2bf9eb5708
namespace CoverCertificatec0f3040bb9

private theorem checked200 : adaptiveCoverCheck 0 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 0 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 0 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 0 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 0 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 0 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 0 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 0 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell213 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 0 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 0 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 0 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 0 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 0 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 0 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 0 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 0 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell313 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 1 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 1 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 1 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 1 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell03 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 1 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 1 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 1 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 1 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 1 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 1 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 1 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 1 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec0f3040bb9

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c0_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012103 = true := by
  exact CoverCertificatec0f3040bb9.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c1_4_00577
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7eefa0b856

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells7eefa0b856

open CertificateCells7eefa0b856
namespace CoverCertificatec5d26eacb3

private theorem checked2200 : adaptiveCoverCheck 0 cell2200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2200 (by decide +kernel)

private theorem checked2201 : adaptiveCoverCheck 0 cell2201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2201 (by decide +kernel)

private theorem checked2202 : adaptiveCoverCheck 0 cell2202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2202 (by decide +kernel)

private theorem checked2203 : adaptiveCoverCheck 0 cell2203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2203 (by decide +kernel)

private theorem checked2210 : adaptiveCoverCheck 0 cell2210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2210 (by decide +kernel)

private theorem checked2211 : adaptiveCoverCheck 0 cell2211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2211 (by decide +kernel)

private theorem checked2212 : adaptiveCoverCheck 0 cell2212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2212 (by decide +kernel)

private theorem checked2213 : adaptiveCoverCheck 0 cell2213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2213 (by decide +kernel)

private theorem checked2300 : adaptiveCoverCheck 0 cell2300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2300 (by decide +kernel)

private theorem checked2301 : adaptiveCoverCheck 0 cell2301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2301 (by decide +kernel)

private theorem checked2302 : adaptiveCoverCheck 0 cell2302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2302 (by decide +kernel)

private theorem checked2303 : adaptiveCoverCheck 0 cell2303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2303 (by decide +kernel)

private theorem checked2310 : adaptiveCoverCheck 0 cell2310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2310 (by decide +kernel)

private theorem checked2311 : adaptiveCoverCheck 0 cell2311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2311 (by decide +kernel)

private theorem checked2312 : adaptiveCoverCheck 0 cell2312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2312 (by decide +kernel)

private theorem checked2313 : adaptiveCoverCheck 0 cell2313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2313 (by decide +kernel)

private theorem checked3200 : adaptiveCoverCheck 0 cell3200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3200 (by decide +kernel)

private theorem checked3201 : adaptiveCoverCheck 0 cell3201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3201 (by decide +kernel)

private theorem checked3202 : adaptiveCoverCheck 0 cell3202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3202 (by decide +kernel)

private theorem checked3203 : adaptiveCoverCheck 0 cell3203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3203 (by decide +kernel)

private theorem checked3210 : adaptiveCoverCheck 0 cell3210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3210 (by decide +kernel)

private theorem checked3211 : adaptiveCoverCheck 0 cell3211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3211 (by decide +kernel)

private theorem checked3212 : adaptiveCoverCheck 0 cell3212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3212 (by decide +kernel)

private theorem checked3213 : adaptiveCoverCheck 0 cell3213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3213 (by decide +kernel)

private theorem checked3300 : adaptiveCoverCheck 0 cell3300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3300 (by decide +kernel)

private theorem checked3301 : adaptiveCoverCheck 0 cell3301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3301 (by decide +kernel)

private theorem checked3302 : adaptiveCoverCheck 0 cell3302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3302 (by decide +kernel)

private theorem checked3303 : adaptiveCoverCheck 0 cell3303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3303 (by decide +kernel)

private theorem checked3310 : adaptiveCoverCheck 0 cell3310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3310 (by decide +kernel)

private theorem checked3311 : adaptiveCoverCheck 0 cell3311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3311 (by decide +kernel)

private theorem checked3312 : adaptiveCoverCheck 0 cell3312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3312 (by decide +kernel)

private theorem checked3313 : adaptiveCoverCheck 0 cell3313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell3313 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell220
    checked2200 checked2201 checked2202 checked2203

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell221
    checked2210 checked2211 checked2212 checked2213

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell230
    checked2300 checked2301 checked2302 checked2303

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell231
    checked2310 checked2311 checked2312 checked2313

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell320
    checked3200 checked3201 checked3202 checked3203

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell321
    checked3210 checked3211 checked3212 checked3213

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell330
    checked3300 checked3301 checked3302 checked3303

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell331
    checked3310 checked3311 checked3312 checked3313

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec5d26eacb3

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificatec5d26eacb3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c2_4_00578
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdb6ef42c13

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsdb6ef42c13

open CertificateCellsdb6ef42c13
namespace CoverCertificate3612aa63be

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3612aa63be

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificate3612aa63be.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c1_c3_4_00579
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells91885e0374

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells91885e0374

open CertificateCells91885e0374
namespace CoverCertificateba32fc9e0a

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateba32fc9e0a

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002001))) = true := by
  exact CoverCertificateba32fc9e0a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c2_5_00581
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsba71b1d520

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsba71b1d520

open CertificateCellsba71b1d520
namespace CoverCertificate2170ad4ca0

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate2170ad4ca0

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c2 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002001)) = true := by
  exact CoverCertificate2170ad4ca0.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c3_5_00582
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells54caf0dec0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells54caf0dec0

open CertificateCells54caf0dec0
namespace CoverCertificate513511aa15

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate513511aa15

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c3 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002001)) = true := by
  exact CoverCertificate513511aa15.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_c0_4_00586
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells22ecf07105

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells22ecf07105

open CertificateCells22ecf07105
namespace CoverCertificate3743e2f873

private theorem checked2200 : adaptiveCoverCheck 0 cell2200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2200 (by decide +kernel)

private theorem checked2201 : adaptiveCoverCheck 0 cell2201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2201 (by decide +kernel)

private theorem checked2202 : adaptiveCoverCheck 0 cell2202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2202 (by decide +kernel)

private theorem checked2203 : adaptiveCoverCheck 0 cell2203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2203 (by decide +kernel)

private theorem checked2210 : adaptiveCoverCheck 0 cell2210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2210 (by decide +kernel)

private theorem checked2211 : adaptiveCoverCheck 0 cell2211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2211 (by decide +kernel)

private theorem checked2212 : adaptiveCoverCheck 0 cell2212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2212 (by decide +kernel)

private theorem checked2213 : adaptiveCoverCheck 0 cell2213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2213 (by decide +kernel)

private theorem checked2300 : adaptiveCoverCheck 0 cell2300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2300 (by decide +kernel)

private theorem checked2301 : adaptiveCoverCheck 0 cell2301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2301 (by decide +kernel)

private theorem checked2302 : adaptiveCoverCheck 0 cell2302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2302 (by decide +kernel)

private theorem checked2303 : adaptiveCoverCheck 0 cell2303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell2303 (by decide +kernel)

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell220
    checked2200 checked2201 checked2202 checked2203

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell221
    checked2210 checked2211 checked2212 checked2213

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell230
    checked2300 checked2301 checked2302 checked2303

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3743e2f873

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate3743e2f873.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_c1_4_00587
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2d236bc977

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2d236bc977

open CertificateCells2d236bc977
namespace CoverCertificate3e2742ca77

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3e2742ca77

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate3e2742ca77.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_c2_4_00588
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfbf08c6815

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsfbf08c6815

open CertificateCellsfbf08c6815
namespace CoverCertificate05d280259b

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate05d280259b

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate05d280259b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c0_c3_4_00589
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb2588049db

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb2588049db

open CertificateCellsb2588049db
namespace CoverCertificate73ec5d89dc

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate73ec5d89dc

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate73ec5d89dc.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_c0_4_00592
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells80702a4342

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells80702a4342

open CertificateCells80702a4342
namespace CoverCertificated1fc30835b

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated1fc30835b

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificated1fc30835b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_c1_4_00593
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfcacd99e70

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsfcacd99e70

open CertificateCellsfcacd99e70
namespace CoverCertificatec03bec1842

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec03bec1842

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificatec03bec1842.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_c2_4_00594
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc63c49e043

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc63c49e043

open CertificateCellsc63c49e043
namespace CoverCertificate854ce4fcce

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate854ce4fcce

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate854ce4fcce.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c1_c3_4_00595
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse2c2881509

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse2c2881509

open CertificateCellse2c2881509
namespace CoverCertificate756063c6fb

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate756063c6fb

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002001))) = true := by
  exact CoverCertificate756063c6fb.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c2_5_00597
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1273bfc545

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells1273bfc545

open CertificateCells1273bfc545
namespace CoverCertificatebb637b4eef

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatebb637b4eef

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002001)) = true := by
  exact CoverCertificatebb637b4eef.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c3_c3_5_00598
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells758d72a450

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells758d72a450

open CertificateCells758d72a450
namespace CoverCertificate7fa5919613

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate7fa5919613

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c3_c3 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002001)) = true := by
  exact CoverCertificate7fa5919613.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above Leaf0000220020_c0_c2_7_00601
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells898eeb07c6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells898eeb07c6

open CertificateCells898eeb07c6
namespace CoverCertificateb766a036ce

private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateb766a036ce

theorem e24KC2ThetaAboveLeaf0000220020_c0_c2 :
    adaptiveCoverCheck 7 thetaAboveCell000022002002 = true := by
  exact CoverCertificateb766a036ce.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above Leaf0000220020_c0_c3_7_00602
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3b9ec898a9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3b9ec898a9

open CertificateCells3b9ec898a9
namespace CoverCertificate61295956d2

private theorem checked00 : adaptiveCoverCheck 5 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 5 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 5 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 5 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 5 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 5 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 5 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 5 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate61295956d2

theorem e24KC2ThetaAboveLeaf0000220020_c0_c3 :
    adaptiveCoverCheck 7 thetaAboveCell000022002003 = true := by
  exact CoverCertificate61295956d2.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c0_6_00606
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellscbef0a66a7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellscbef0a66a7

open CertificateCellscbef0a66a7
namespace CoverCertificate828511f0b8

private theorem checked20 : adaptiveCoverCheck 4 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 4 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 4 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 4 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 4 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 4 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 4 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 4 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate828511f0b8

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c0 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022002010) = true := by
  exact CoverCertificate828511f0b8.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c1_6_00607
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0e30799078

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0e30799078

open CertificateCells0e30799078
namespace CoverCertificated54c339469

private theorem checked20 : adaptiveCoverCheck 4 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 4 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 4 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 4 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 4 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 4 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 4 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 4 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated54c339469

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022002010) = true := by
  exact CoverCertificated54c339469.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_c0_4_00610
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsaa7ab31314

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsaa7ab31314

open CertificateCellsaa7ab31314
namespace CoverCertificate4dd8dcfac0

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4dd8dcfac0

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificate4dd8dcfac0.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_c1_4_00611
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa4a7cbe7b2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa4a7cbe7b2

open CertificateCellsa4a7cbe7b2
namespace CoverCertificate4ee27c37fd

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4ee27c37fd

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificate4ee27c37fd.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_c2_4_00612
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9f358cc74d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells9f358cc74d

open CertificateCells9f358cc74d
namespace CoverCertificated7b655454c

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated7b655454c

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificated7b655454c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c0_c3_4_00613
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf2bd9cd8f9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsf2bd9cd8f9

open CertificateCellsf2bd9cd8f9
namespace CoverCertificate34bc1a6525

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate34bc1a6525

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificate34bc1a6525.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_c0_4_00616
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse30fe464b6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse30fe464b6

open CertificateCellse30fe464b6
namespace CoverCertificate6e40ca0512

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate6e40ca0512

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificate6e40ca0512.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_c1_4_00617
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells50e57ae8a7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells50e57ae8a7

open CertificateCells50e57ae8a7
namespace CoverCertificateefd035cf65

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateefd035cf65

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificateefd035cf65.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_c2_4_00618
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6831b5295c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6831b5295c

open CertificateCells6831b5295c
namespace CoverCertificatea4b667aaa0

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea4b667aaa0

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificatea4b667aaa0.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c1_c3_4_00619
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6ec7ee0b32

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6ec7ee0b32

open CertificateCells6ec7ee0b32
namespace CoverCertificateccad0dc048

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateccad0dc048

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002010))) = true := by
  exact CoverCertificateccad0dc048.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c2_5_00621
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellscdb025ab65

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellscdb025ab65

open CertificateCellscdb025ab65
namespace CoverCertificate89deca0334

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate89deca0334

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c2 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002010)) = true := by
  exact CoverCertificate89deca0334.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c2_c3_5_00622
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells251eb00cd5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells251eb00cd5

open CertificateCells251eb00cd5
namespace CoverCertificate8778f820bd

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate8778f820bd

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c2_c3 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002010)) = true := by
  exact CoverCertificate8778f820bd.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_c0_4_00626
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb46fd93863

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb46fd93863

open CertificateCellsb46fd93863
namespace CoverCertificatef14d24461a

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatef14d24461a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c0 :
    adaptiveCoverCheck 4 (childLL (childLL (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificatef14d24461a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_c1_4_00627
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells02c02b7fd3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells02c02b7fd3

open CertificateCells02c02b7fd3
namespace CoverCertificate79980b2e6c

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate79980b2e6c

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c1 :
    adaptiveCoverCheck 4 (childLH (childLL (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate79980b2e6c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_c2_4_00628
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells969e2199d5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells969e2199d5

open CertificateCells969e2199d5
namespace CoverCertificateed2ff1f24e

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateed2ff1f24e

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificateed2ff1f24e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c0_c3_4_00629
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells99f6185557

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells99f6185557

open CertificateCells99f6185557
namespace CoverCertificate4bcf50db3e

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4bcf50db3e

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate4bcf50db3e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_c0_4_00632
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsea3eb05dc6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsea3eb05dc6

open CertificateCellsea3eb05dc6
namespace CoverCertificate1e4788169b

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1e4788169b

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c0 :
    adaptiveCoverCheck 4 (childLL (childLH (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate1e4788169b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_c1_4_00633
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1daa3566d0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells1daa3566d0

open CertificateCells1daa3566d0
namespace CoverCertificate4f5a63a5df

private theorem checked220 : adaptiveCoverCheck 1 cell220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell220 (by decide +kernel)

private theorem checked221 : adaptiveCoverCheck 1 cell221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell221 (by decide +kernel)

private theorem checked222 : adaptiveCoverCheck 1 cell222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell222 (by decide +kernel)

private theorem checked223 : adaptiveCoverCheck 1 cell223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell223 (by decide +kernel)

private theorem checked230 : adaptiveCoverCheck 1 cell230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell230 (by decide +kernel)

private theorem checked231 : adaptiveCoverCheck 1 cell231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell231 (by decide +kernel)

private theorem checked232 : adaptiveCoverCheck 1 cell232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell232 (by decide +kernel)

private theorem checked233 : adaptiveCoverCheck 1 cell233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell233 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 1 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 1 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 1 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 1 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 1 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 1 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 1 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 1 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell333 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4f5a63a5df

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c1 :
    adaptiveCoverCheck 4 (childLH (childLH (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate4f5a63a5df.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_c2_4_00634
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells04b8a575e1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells04b8a575e1

open CertificateCells04b8a575e1
namespace CoverCertificate89bb9fd21e

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate89bb9fd21e

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate89bb9fd21e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c1_c3_4_00635
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb52fa9450d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb52fa9450d

open CertificateCellsb52fa9450d
namespace CoverCertificate5c80136736

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5c80136736

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002010))) = true := by
  exact CoverCertificate5c80136736.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c2_5_00637
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells75262755f1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells75262755f1

open CertificateCells75262755f1
namespace CoverCertificate645f79320a

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate645f79320a

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002010)) = true := by
  exact CoverCertificate645f79320a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c1_c0_c3_c3_5_00638
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells88775d9be2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells88775d9be2

open CertificateCells88775d9be2
namespace CoverCertificate3e0a4a2c6f

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3e0a4a2c6f

theorem e24KC2ThetaAboveLeaf0000220020_c1_c0_c3_c3 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002010)) = true := by
  exact CoverCertificate3e0a4a2c6f.checkedRoot

end PartE
end GerverSofa

end

end

end

end

end

end
