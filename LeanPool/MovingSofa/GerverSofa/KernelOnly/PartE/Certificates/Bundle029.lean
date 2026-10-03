/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch042`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CoverCertificate09deb4be62

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH (childHL (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificate09deb4be62

namespace GerverSofa.PartE.CoverCertificate80b49a8860

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLH (childHL (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificate80b49a8860

namespace GerverSofa.PartE.CoverCertificate8fa79bb108

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHL (childLL (childLL (childLL (childHL (childLL (childLL (childHL
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

private abbrev cell1100 : AngleCell :=
  childLL cell110

private abbrev cell1101 : AngleCell :=
  childLH cell110

private abbrev cell1102 : AngleCell :=
  childHL cell110

private abbrev cell1103 : AngleCell :=
  childHH cell110

private abbrev cell1110 : AngleCell :=
  childLL cell111

private abbrev cell1111 : AngleCell :=
  childLH cell111

private abbrev cell1112 : AngleCell :=
  childHL cell111

private abbrev cell1113 : AngleCell :=
  childHH cell111

end GerverSofa.PartE.CoverCertificate8fa79bb108

namespace GerverSofa.PartE.CoverCertificate9198440329

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHL (childLL (childLL (childLL (childHL (childLL (childLL (childHL
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

private abbrev cell1100 : AngleCell :=
  childLL cell110

private abbrev cell1101 : AngleCell :=
  childLH cell110

private abbrev cell1102 : AngleCell :=
  childHL cell110

private abbrev cell1103 : AngleCell :=
  childHH cell110

private abbrev cell1110 : AngleCell :=
  childLL cell111

private abbrev cell1111 : AngleCell :=
  childLH cell111

private abbrev cell1112 : AngleCell :=
  childHL cell111

private abbrev cell1113 : AngleCell :=
  childHH cell111

end GerverSofa.PartE.CoverCertificate9198440329

namespace GerverSofa.PartE.CoverCertificate54d2ea68c4

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childLL (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate54d2ea68c4

namespace GerverSofa.PartE.CoverCertificate9a90f66090

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childLL (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate9a90f66090

namespace GerverSofa.PartE.CoverCertificate9a54be935a

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL
    (childHL (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate9a54be935a

namespace GerverSofa.PartE.CoverCertificatea35db1f021

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL
    (childHL (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea35db1f021

namespace GerverSofa.PartE.CoverCertificate8333a307a4

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificate8333a307a4

namespace GerverSofa.PartE.CoverCertificated46e97b4d3

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificated46e97b4d3

namespace GerverSofa.PartE.CoverCertificate39bdb9b52b

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL
    (childHL (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate39bdb9b52b

namespace GerverSofa.PartE.CoverCertificate21662757e3

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL
    (childHL (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate21662757e3

namespace GerverSofa.PartE.CoverCertificate7ec8971130

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificate7ec8971130

namespace GerverSofa.PartE.CoverCertificatec012db59ec

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificatec012db59ec

namespace GerverSofa.PartE.CoverCertificate418c92a9a1

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL (childHL
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

private abbrev cell1100 : AngleCell :=
  childLL cell110

private abbrev cell1101 : AngleCell :=
  childLH cell110

private abbrev cell1102 : AngleCell :=
  childHL cell110

private abbrev cell1103 : AngleCell :=
  childHH cell110

private abbrev cell1110 : AngleCell :=
  childLL cell111

private abbrev cell1111 : AngleCell :=
  childLH cell111

private abbrev cell1112 : AngleCell :=
  childHL cell111

private abbrev cell1113 : AngleCell :=
  childHH cell111

end GerverSofa.PartE.CoverCertificate418c92a9a1

namespace GerverSofa.PartE.CoverCertificate69c64655e6

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHH (childLL (childLL (childLL (childHL (childLL (childLL (childHL
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

private abbrev cell1100 : AngleCell :=
  childLL cell110

private abbrev cell1101 : AngleCell :=
  childLH cell110

private abbrev cell1102 : AngleCell :=
  childHL cell110

private abbrev cell1103 : AngleCell :=
  childHH cell110

private abbrev cell1110 : AngleCell :=
  childLL cell111

private abbrev cell1111 : AngleCell :=
  childLH cell111

private abbrev cell1112 : AngleCell :=
  childHL cell111

private abbrev cell1113 : AngleCell :=
  childHH cell111

end GerverSofa.PartE.CoverCertificate69c64655e6

namespace GerverSofa.PartE.CoverCertificateca69cb479d

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLH (childHH (childLL (childLL (childLL (childHL (childLL (childLL
    (childHL (childHL (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateca69cb479d

namespace GerverSofa.PartE.CoverCertificate25b8e68ebd

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH (childHH (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificate25b8e68ebd

namespace GerverSofa.PartE.CoverCertificate0b5492bc32

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH (childHH (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificate0b5492bc32

namespace GerverSofa.PartE.CoverCertificatec2a3e401f5

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH (childHH (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificatec2a3e401f5

namespace GerverSofa.PartE.CoverCertificatee2dbedfd13

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLH (childHH (childLL (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificatee2dbedfd13

namespace GerverSofa.PartE.CoverCertificate558b871c6c

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHH (childLL (childLL (childLL (childHL (childLL (childLL (childHL
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

private abbrev cell1100 : AngleCell :=
  childLL cell110

private abbrev cell1101 : AngleCell :=
  childLH cell110

private abbrev cell1102 : AngleCell :=
  childHL cell110

private abbrev cell1103 : AngleCell :=
  childHH cell110

private abbrev cell1110 : AngleCell :=
  childLL cell111

private abbrev cell1111 : AngleCell :=
  childLH cell111

private abbrev cell1112 : AngleCell :=
  childHL cell111

private abbrev cell1113 : AngleCell :=
  childHH cell111

end GerverSofa.PartE.CoverCertificate558b871c6c

namespace GerverSofa.PartE.CoverCertificatec90af2cbcd

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHH (childLL (childLL (childLL (childHL (childLL (childLL (childHL
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

private abbrev cell1100 : AngleCell :=
  childLL cell110

private abbrev cell1101 : AngleCell :=
  childLH cell110

private abbrev cell1102 : AngleCell :=
  childHL cell110

private abbrev cell1103 : AngleCell :=
  childHH cell110

private abbrev cell1110 : AngleCell :=
  childLL cell111

private abbrev cell1111 : AngleCell :=
  childLH cell111

private abbrev cell1112 : AngleCell :=
  childHL cell111

private abbrev cell1113 : AngleCell :=
  childHH cell111

end GerverSofa.PartE.CoverCertificatec90af2cbcd

namespace GerverSofa.PartE.CoverCertificate850c59f3da

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childLL (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate850c59f3da

namespace GerverSofa.PartE.CoverCertificate1c095a90b4

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childLL (childLL (childLL (childHL (childLL (childLL (childHL (childHL
    (childLL (childLL (childLL (childLL (e24ThetaAboveRoot)))))))))))))))

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate1c095a90b4

namespace GerverSofa.PartE.CoverCertificate0341d165df

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLL
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

end GerverSofa.PartE.CoverCertificate0341d165df

namespace GerverSofa.PartE.CoverCertificatedfaaa383f3

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLL (childLL (childHL (childLL (childLL (childHL (childHL (childLL
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

end GerverSofa.PartE.CoverCertificatedfaaa383f3

namespace GerverSofa.PartE.CoverCertificatea8d5b0d3f5

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL (childHL (childLH (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificatea8d5b0d3f5

namespace GerverSofa.PartE.CoverCertificate0573161232

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL (childHL (childLH (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificate0573161232

namespace GerverSofa.PartE.CoverCertificate4fc67a95c3

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLL (childHL (childLH (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificate4fc67a95c3

namespace GerverSofa.PartE.CoverCertificateba1f6e5865

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLL (childHL (childLH (childLL (childLL (childHL (childLL (childLL
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

end GerverSofa.PartE.CoverCertificateba1f6e5865

namespace GerverSofa.PartE.CertificateCells508bd70e72

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells508bd70e72

namespace GerverSofa.PartE.CertificateCells2ebb3ae727

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells2ebb3ae727

namespace GerverSofa.PartE.CertificateCells808549b800

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells808549b800

namespace GerverSofa.PartE.CertificateCellsd717193e27

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsd717193e27

namespace GerverSofa.PartE.CertificateCellsc9eea5ae86

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsc9eea5ae86

namespace GerverSofa.PartE.CertificateCells883d9c2359

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells883d9c2359

namespace GerverSofa.PartE.CertificateCells81adac8f59

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells81adac8f59

namespace GerverSofa.PartE.CertificateCellsd02c0d99aa

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCellsd02c0d99aa

namespace GerverSofa.PartE.CertificateCellsb3e2fb602b

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCellsb3e2fb602b

namespace GerverSofa.PartE.CertificateCells4e515808c8

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells4e515808c8

namespace GerverSofa.PartE.CertificateCellsc37a4f0e7c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCellsc37a4f0e7c

namespace GerverSofa.PartE.CertificateCells6662eefeaf

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells6662eefeaf

namespace GerverSofa.PartE.CertificateCells9cbe967e81

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells9cbe967e81

namespace GerverSofa.PartE.CertificateCells868d9f8f69

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells868d9f8f69

namespace GerverSofa.PartE.CertificateCells3c1ed7e077

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells3c1ed7e077

namespace GerverSofa.PartE.CertificateCellsda1171cd1c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsda1171cd1c

namespace GerverSofa.PartE.CertificateCells00487431af

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells00487431af

namespace GerverSofa.PartE.CertificateCellsebfda2d52e

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCellsebfda2d52e

namespace GerverSofa.PartE.CertificateCells0d7543751e

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells0d7543751e

namespace GerverSofa.PartE.CertificateCells3d57dcf8b1

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells3d57dcf8b1

namespace GerverSofa.PartE.CertificateCells280bbc9838

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells280bbc9838

namespace GerverSofa.PartE.CertificateCells86fd793561

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells86fd793561

namespace GerverSofa.PartE.CertificateCellsc0e73f28b6

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCellsc0e73f28b6

namespace GerverSofa.PartE.CertificateCells97ab098fbd

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell000022002000)))

end GerverSofa.PartE.CertificateCells97ab098fbd

namespace GerverSofa.PartE.CertificateCells90296eb122

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells90296eb122

namespace GerverSofa.PartE.CertificateCells48c4f5a54f

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells48c4f5a54f

namespace GerverSofa.PartE.CertificateCellsd47d097993

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCellsd47d097993

namespace GerverSofa.PartE.CertificateCells861c7fa81d

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells861c7fa81d

namespace GerverSofa.PartE.CertificateCells96a538a32c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells96a538a32c

namespace GerverSofa.PartE.CertificateCells867b92c925

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

end GerverSofa.PartE.CertificateCells867b92c925

namespace GerverSofa.PartE.CertificateCellse8beb6dc5c

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCellse8beb6dc5c

namespace GerverSofa.PartE.CertificateCellsa4fa334623

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCellsa4fa334623

namespace GerverSofa.PartE.CertificateCellsd70a3df0a0

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCellsd70a3df0a0

namespace GerverSofa.PartE.CertificateCells02a2748806

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCells02a2748806

namespace GerverSofa.PartE.CertificateCells3863a30667

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCells3863a30667

namespace GerverSofa.PartE.CertificateCellsd6d3f4989a

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCellsd6d3f4989a

namespace GerverSofa.PartE.CertificateCellsb420376865

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCellsb420376865

namespace GerverSofa.PartE.CertificateCellsa9306cab0b

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002200)))

/-- Subcell `0000220020012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220020012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell000022002001)))

end GerverSofa.PartE.CertificateCellsa9306cab0b

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.ThetaAbove.Leaf00504`.
* `KernelOnly.PartE.ThetaAbove.Leaf00505`.
* `KernelOnly.PartE.ThetaAbove.Leaf00507`.
* `KernelOnly.PartE.ThetaAbove.Leaf00508`.
* `KernelOnly.PartE.ThetaAbove.Leaf00510`.
* `KernelOnly.PartE.ThetaAbove.Leaf00511`.
* `KernelOnly.PartE.ThetaAbove.Leaf00516`.
* `KernelOnly.PartE.ThetaAbove.Leaf00517`.
* `KernelOnly.PartE.ThetaAbove.Leaf00518`.
* `KernelOnly.PartE.ThetaAbove.Leaf00519`.
* `KernelOnly.PartE.ThetaAbove.Leaf00522`.
* `KernelOnly.PartE.ThetaAbove.Leaf00523`.
* `KernelOnly.PartE.ThetaAbove.Leaf00524`.
* `KernelOnly.PartE.ThetaAbove.Leaf00525`.
* `KernelOnly.PartE.ThetaAbove.Leaf00527`.
* `KernelOnly.PartE.ThetaAbove.Leaf00528`.
* `KernelOnly.PartE.ThetaAbove.Leaf00532`.
* `KernelOnly.PartE.ThetaAbove.Leaf00533`.
* `KernelOnly.PartE.ThetaAbove.Leaf00534`.
* `KernelOnly.PartE.ThetaAbove.Leaf00535`.
* `KernelOnly.PartE.ThetaAbove.Leaf00538`.
* `KernelOnly.PartE.ThetaAbove.Leaf00539`.
* `KernelOnly.PartE.ThetaAbove.Leaf00540`.
* `KernelOnly.PartE.ThetaAbove.Leaf00541`.
* `KernelOnly.PartE.ThetaAbove.Leaf00543`.
* `KernelOnly.PartE.ThetaAbove.Leaf00544`.
* `KernelOnly.PartE.ThetaAbove.Leaf00546`.
* `KernelOnly.PartE.ThetaAbove.Leaf00547`.
* `KernelOnly.PartE.ThetaAbove.Leaf00551`.
* `KernelOnly.PartE.ThetaAbove.Leaf00552`.
* `KernelOnly.PartE.ThetaAbove.Leaf00556`.
* `KernelOnly.PartE.ThetaAbove.Leaf00557`.
* `KernelOnly.PartE.ThetaAbove.Leaf00558`.
* `KernelOnly.PartE.ThetaAbove.Leaf00559`.
* `KernelOnly.PartE.ThetaAbove.Leaf00562`.
* `KernelOnly.PartE.ThetaAbove.Leaf00563`.
* `KernelOnly.PartE.ThetaAbove.Leaf00564`.
* `KernelOnly.PartE.ThetaAbove.Leaf00565`.
-/

public section

noncomputable section

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c1_c2_3_00504
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells508bd70e72

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells508bd70e72

open CertificateCells508bd70e72
namespace CoverCertificate09deb4be62

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

end CoverCertificate09deb4be62

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002112 = true := by
  exact CoverCertificate09deb4be62.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c1_c3_3_00505
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2ebb3ae727

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2ebb3ae727

open CertificateCells2ebb3ae727
namespace CoverCertificate80b49a8860

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

end CoverCertificate80b49a8860

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c1_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020002113 = true := by
  exact CoverCertificate80b49a8860.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c2_4_00507
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells808549b800

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells808549b800

open CertificateCells808549b800
namespace CoverCertificate8fa79bb108

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

private theorem checked1100 : adaptiveCoverCheck 0 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 0 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 0 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 0 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 0 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 0 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 0 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 0 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1113 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 0 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell111
    checked1110 checked1111 checked1112 checked1113

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

end CoverCertificate8fa79bb108

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHL thetaAboveCell000022002000))) = true := by
  exact CoverCertificate8fa79bb108.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c1_c3_4_00508
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd717193e27

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd717193e27

open CertificateCellsd717193e27
namespace CoverCertificate9198440329

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

private theorem checked1100 : adaptiveCoverCheck 0 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 0 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 0 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 0 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 0 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 0 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 0 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 0 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1113 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 0 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell111
    checked1110 checked1111 checked1112 checked1113

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

end CoverCertificate9198440329

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHL thetaAboveCell000022002000))) = true := by
  exact CoverCertificate9198440329.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c2_5_00510
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc9eea5ae86

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc9eea5ae86

open CertificateCellsc9eea5ae86
namespace CoverCertificate54d2ea68c4

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

end CoverCertificate54d2ea68c4

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c2 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022002000)) = true := by
  exact CoverCertificate54d2ea68c4.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c2_c3_5_00511
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells883d9c2359

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells883d9c2359

open CertificateCells883d9c2359
namespace CoverCertificate9a90f66090

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

end CoverCertificate9a90f66090

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c2_c3 :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022002000)) = true := by
  exact CoverCertificate9a90f66090.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c0_c0_3_00516
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells81adac8f59

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells81adac8f59

open CertificateCells81adac8f59
namespace CoverCertificate9a54be935a

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate9a54be935a

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003000 = true := by
  exact CoverCertificate9a54be935a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c0_c1_3_00517
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd02c0d99aa

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd02c0d99aa

open CertificateCellsd02c0d99aa
namespace CoverCertificatea35db1f021

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea35db1f021

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003001 = true := by
  exact CoverCertificatea35db1f021.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c0_c2_3_00518
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb3e2fb602b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb3e2fb602b

open CertificateCellsb3e2fb602b
namespace CoverCertificate8333a307a4

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

end CoverCertificate8333a307a4

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003002 = true := by
  exact CoverCertificate8333a307a4.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c0_c3_3_00519
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4e515808c8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells4e515808c8

open CertificateCells4e515808c8
namespace CoverCertificated46e97b4d3

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

end CoverCertificated46e97b4d3

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c0_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003003 = true := by
  exact CoverCertificated46e97b4d3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c1_c0_3_00522
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc37a4f0e7c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc37a4f0e7c

open CertificateCellsc37a4f0e7c
namespace CoverCertificate39bdb9b52b

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate39bdb9b52b

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003010 = true := by
  exact CoverCertificate39bdb9b52b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c1_c1_3_00523
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6662eefeaf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells6662eefeaf

open CertificateCells6662eefeaf
namespace CoverCertificate21662757e3

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate21662757e3

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003011 = true := by
  exact CoverCertificate21662757e3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c1_c2_3_00524
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9cbe967e81

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells9cbe967e81

open CertificateCells9cbe967e81
namespace CoverCertificate7ec8971130

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

end CoverCertificate7ec8971130

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003012 = true := by
  exact CoverCertificate7ec8971130.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c1_c3_3_00525
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells868d9f8f69

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells868d9f8f69

open CertificateCells868d9f8f69
namespace CoverCertificatec012db59ec

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

end CoverCertificatec012db59ec

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c1_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003013 = true := by
  exact CoverCertificatec012db59ec.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c2_4_00527
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3c1ed7e077

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3c1ed7e077

open CertificateCells3c1ed7e077
namespace CoverCertificate418c92a9a1

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

private theorem checked1100 : adaptiveCoverCheck 0 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 0 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 0 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 0 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 0 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 0 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 0 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 0 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1113 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 0 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell111
    checked1110 checked1111 checked1112 checked1113

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

end CoverCertificate418c92a9a1

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c2 :
    adaptiveCoverCheck 4 (childHL (childLL (childHH thetaAboveCell000022002000))) = true := by
  exact CoverCertificate418c92a9a1.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c0_c3_4_00528
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsda1171cd1c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsda1171cd1c

open CertificateCellsda1171cd1c
namespace CoverCertificate69c64655e6

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

private theorem checked1100 : adaptiveCoverCheck 0 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 0 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 0 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 0 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 0 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 0 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 0 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 0 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1113 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 0 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell111
    checked1110 checked1111 checked1112 checked1113

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

end CoverCertificate69c64655e6

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c0_c3 :
    adaptiveCoverCheck 4 (childHH (childLL (childHH thetaAboveCell000022002000))) = true := by
  exact CoverCertificate69c64655e6.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c0_c0_3_00532
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells00487431af

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells00487431af

open CertificateCells00487431af
namespace CoverCertificateca69cb479d

private theorem checked0 : adaptiveCoverCheck 2 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 2 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 2 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 2 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 3 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateca69cb479d

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003100 = true := by
  exact CoverCertificateca69cb479d.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c0_c1_3_00533
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsebfda2d52e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsebfda2d52e

open CertificateCellsebfda2d52e
theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003101 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c0_c2_3_00534
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0d7543751e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells0d7543751e

open CertificateCells0d7543751e
namespace CoverCertificate25b8e68ebd

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

end CoverCertificate25b8e68ebd

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003102 = true := by
  exact CoverCertificate25b8e68ebd.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c0_c3_3_00535
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3d57dcf8b1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3d57dcf8b1

open CertificateCells3d57dcf8b1
namespace CoverCertificate0b5492bc32

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

end CoverCertificate0b5492bc32

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c0_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003103 = true := by
  exact CoverCertificate0b5492bc32.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c1_c0_3_00538
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells280bbc9838

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells280bbc9838

open CertificateCells280bbc9838
theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003110 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c1_c1_3_00539
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells86fd793561

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells86fd793561

open CertificateCells86fd793561
theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003111 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c1_c2_3_00540
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc0e73f28b6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsc0e73f28b6

open CertificateCellsc0e73f28b6
namespace CoverCertificatec2a3e401f5

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

end CoverCertificatec2a3e401f5

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003112 = true := by
  exact CoverCertificatec2a3e401f5.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c1_c3_3_00541
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells97ab098fbd

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells97ab098fbd

open CertificateCells97ab098fbd
namespace CoverCertificatee2dbedfd13

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

end CoverCertificatee2dbedfd13

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c1_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020003113 = true := by
  exact CoverCertificatee2dbedfd13.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c2_4_00543
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells90296eb122

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells90296eb122

open CertificateCells90296eb122
namespace CoverCertificate558b871c6c

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

private theorem checked1100 : adaptiveCoverCheck 0 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 0 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 0 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 0 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 0 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 0 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 0 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 0 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1113 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 0 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell111
    checked1110 checked1111 checked1112 checked1113

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

end CoverCertificate558b871c6c

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c2 :
    adaptiveCoverCheck 4 (childHL (childLH (childHH thetaAboveCell000022002000))) = true := by
  exact CoverCertificate558b871c6c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c1_c3_4_00544
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells48c4f5a54f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells48c4f5a54f

open CertificateCells48c4f5a54f
namespace CoverCertificatec90af2cbcd

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

private theorem checked1100 : adaptiveCoverCheck 0 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 0 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 0 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 0 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 0 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 0 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 0 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 0 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1113 (by decide +kernel)

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
  exact adaptiveCoverCheck_succ_of_children 0 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell111
    checked1110 checked1111 checked1112 checked1113

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

end CoverCertificatec90af2cbcd

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c1_c3 :
    adaptiveCoverCheck 4 (childHH (childLH (childHH thetaAboveCell000022002000))) = true := by
  exact CoverCertificatec90af2cbcd.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c2_5_00546
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd47d097993

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd47d097993

open CertificateCellsd47d097993
namespace CoverCertificate850c59f3da

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

end CoverCertificate850c59f3da

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c2 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022002000)) = true := by
  exact CoverCertificate850c59f3da.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c0_c3_c3_5_00547
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells861c7fa81d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells861c7fa81d

open CertificateCells861c7fa81d
namespace CoverCertificate1c095a90b4

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

end CoverCertificate1c095a90b4

theorem e24KC2ThetaAboveLeaf0000220020_c0_c0_c3_c3 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002000)) = true := by
  exact CoverCertificate1c095a90b4.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c0_6_00551
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells96a538a32c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells96a538a32c

open CertificateCells96a538a32c
namespace CoverCertificate0341d165df

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

end CoverCertificate0341d165df

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c0 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022002001) = true := by
  exact CoverCertificate0341d165df.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c1_6_00552
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells867b92c925

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells867b92c925

open CertificateCells867b92c925
namespace CoverCertificatedfaaa383f3

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

end CoverCertificatedfaaa383f3

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022002001) = true := by
  exact CoverCertificatedfaaa383f3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c0_c0_3_00556
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse8beb6dc5c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse8beb6dc5c

open CertificateCellse8beb6dc5c
theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012000 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c0_c1_3_00557
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa4fa334623

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa4fa334623

open CertificateCellsa4fa334623
theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012001 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c0_c2_3_00558
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd70a3df0a0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd70a3df0a0

open CertificateCellsd70a3df0a0
namespace CoverCertificatea8d5b0d3f5

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

end CoverCertificatea8d5b0d3f5

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012002 = true := by
  exact CoverCertificatea8d5b0d3f5.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c0_c3_3_00559
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells02a2748806

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells02a2748806

open CertificateCells02a2748806
namespace CoverCertificate0573161232

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

end CoverCertificate0573161232

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c0_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012003 = true := by
  exact CoverCertificate0573161232.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c1_c0_3_00562
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3863a30667

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells3863a30667

open CertificateCells3863a30667
theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1_c0 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012010 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c1_c1_3_00563
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd6d3f4989a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsd6d3f4989a

open CertificateCellsd6d3f4989a
theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1_c1 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012011 = true := by
  decide +kernel

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c1_c2_3_00564
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb420376865

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsb420376865

open CertificateCellsb420376865
namespace CoverCertificate4fc67a95c3

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

end CoverCertificate4fc67a95c3

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1_c2 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012012 = true := by
  exact CoverCertificate4fc67a95c3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Theta Above
Leaf0000220020_c0_c1_c2_c0_c1_c3_3_00565
-/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa9306cab0b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsa9306cab0b

open CertificateCellsa9306cab0b
namespace CoverCertificateba1f6e5865

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

end CoverCertificateba1f6e5865

theorem e24KC2ThetaAboveLeaf0000220020_c0_c1_c2_c0_c1_c3 :
    adaptiveCoverCheck 3 thetaAboveCell0000220020012013 = true := by
  exact CoverCertificateba1f6e5865.checkedRoot

end PartE
end GerverSofa

end

end

end

end

end

end
