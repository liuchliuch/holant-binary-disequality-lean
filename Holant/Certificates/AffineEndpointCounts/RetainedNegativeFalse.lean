import Holant.Certificates.AffineEndpointCounts.RetainedRoutesFalse
namespace Holant.Certificates.AffineEndpointCounts
open Holant.Certificates.AffineEndpoint Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false

 theorem retained_false_000 (c : Fin 1) (hr : BaseRetained 0 c.val false) :
    (0,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 0 false 0 packetData0055 (candidatePairList false)
    packetPass0055 route0055 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_001 (c : Fin 1) (hr : BaseRetained 1 c.val false) :
    (1,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 1 false 0 packetData0056 (candidatePairList false)
    packetPass0056 route0056 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_002 (c : Fin 1) (hr : BaseRetained 2 c.val false) :
    (2,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 2 false 0 packetData0057 (candidatePairList false)
    packetPass0057 route0057 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_003 (c : Fin 1) (hr : BaseRetained 3 c.val false) :
    (3,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 3 false 0 packetData0058 (candidatePairList false)
    packetPass0058 route0058 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_004 (c : Fin 1) (hr : BaseRetained 4 c.val false) :
    (4,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 4 false 0 packetData0059 (candidatePairList false)
    packetPass0059 route0059 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_005 (c : Fin 1) (hr : BaseRetained 5 c.val false) :
    (5,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 5 false 0 packetData0060 (candidatePairList false)
    packetPass0060 route0060 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_006 (c : Fin 1) (hr : BaseRetained 6 c.val false) :
    (6,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 6 false 0 packetData0061 (candidatePairList false)
    packetPass0061 route0061 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_007 (c : Fin 1) (hr : BaseRetained 7 c.val false) :
    (7,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 7 false 0 packetData0062 (candidatePairList false)
    packetPass0062 route0062 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_008 (c : Fin 1) (hr : BaseRetained 8 c.val false) :
    (8,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 8 false 0 packetData0063 (candidatePairList false)
    packetPass0063 route0063 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_009 (c : Fin 1) (hr : BaseRetained 9 c.val false) :
    (9,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 9 false 0 packetData0064 (candidatePairList false)
    packetPass0064 route0064 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_010 (c : Fin 1) (hr : BaseRetained 10 c.val false) :
    (10,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 10 false 0 packetData0065 (candidatePairList false)
    packetPass0065 route0065 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_011 (c : Fin 1) (hr : BaseRetained 11 c.val false) :
    (11,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 11 false 0 packetData0066 (candidatePairList false)
    packetPass0066 route0066 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_012 (c : Fin 1) (hr : BaseRetained 12 c.val false) :
    (12,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 12 false 0 packetData0067 (candidatePairList false)
    packetPass0067 route0067 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_013 (c : Fin 1) (hr : BaseRetained 13 c.val false) :
    (13,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 13 false 0 packetData0068 (candidatePairList false)
    packetPass0068 route0068 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_014 (c : Fin 1) (hr : BaseRetained 14 c.val false) :
    (14,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 14 false 0 packetData0069 (candidatePairList false)
    packetPass0069 route0069 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_015 (c : Fin 1) (hr : BaseRetained 15 c.val false) :
    (15,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 15 false 0 packetData0070 (candidatePairList false)
    packetPass0070 route0070 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_016 (c : Fin 4) (hr : BaseRetained 16 c.val false) :
    (16,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 16 false 0 packetData0071 (candidatePairList false)
    packetPass0071 route0071 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_017 (c : Fin 4) (hr : BaseRetained 17 c.val false) :
    (17,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 17 false 0 packetData0072 (candidatePairList false)
    packetPass0072 route0072 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_018 (c : Fin 4) (hr : BaseRetained 18 c.val false) :
    (18,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 18 false 0 packetData0073 (candidatePairList false)
    packetPass0073 route0073 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_019 (c : Fin 4) (hr : BaseRetained 19 c.val false) :
    (19,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 19 false 0 packetData0074 (candidatePairList false)
    packetPass0074 route0074 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_020 (c : Fin 4) (hr : BaseRetained 20 c.val false) :
    (20,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 20 false 0 packetData0075 (candidatePairList false)
    packetPass0075 route0075 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_021 (c : Fin 4) (hr : BaseRetained 21 c.val false) :
    (21,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 21 false 0 packetData0076 (candidatePairList false)
    packetPass0076 route0076 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_022 (c : Fin 4) (hr : BaseRetained 22 c.val false) :
    (22,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 22 false 0 packetData0077 (candidatePairList false)
    packetPass0077 route0077 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_023 (c : Fin 4) (hr : BaseRetained 23 c.val false) :
    (23,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 23 false 0 packetData0078 (candidatePairList false)
    packetPass0078 route0078 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_024 (c : Fin 4) (hr : BaseRetained 24 c.val false) :
    (24,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 24 false 0 packetData0079 (candidatePairList false)
    packetPass0079 route0079 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_025 (c : Fin 4) (hr : BaseRetained 25 c.val false) :
    (25,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 25 false 0 packetData0080 (candidatePairList false)
    packetPass0080 route0080 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_026 (c : Fin 4) (hr : BaseRetained 26 c.val false) :
    (26,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 26 false 0 packetData0081 (candidatePairList false)
    packetPass0081 route0081 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_027 (c : Fin 4) (hr : BaseRetained 27 c.val false) :
    (27,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 27 false 0 packetData0082 (candidatePairList false)
    packetPass0082 route0082 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_028 (c : Fin 4) (hr : BaseRetained 28 c.val false) :
    (28,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 28 false 0 packetData0083 (candidatePairList false)
    packetPass0083 route0083 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_029 (c : Fin 4) (hr : BaseRetained 29 c.val false) :
    (29,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 29 false 0 packetData0084 (candidatePairList false)
    packetPass0084 route0084 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_030 (c : Fin 4) (hr : BaseRetained 30 c.val false) :
    (30,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 30 false 0 packetData0085 (candidatePairList false)
    packetPass0085 route0085 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_031 (c : Fin 4) (hr : BaseRetained 31 c.val false) :
    (31,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 31 false 0 packetData0086 (candidatePairList false)
    packetPass0086 route0086 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_032 (c : Fin 4) (hr : BaseRetained 32 c.val false) :
    (32,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 32 false 0 packetData0087 (candidatePairList false)
    packetPass0087 route0087 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_033 (c : Fin 4) (hr : BaseRetained 33 c.val false) :
    (33,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 33 false 0 packetData0088 (candidatePairList false)
    packetPass0088 route0088 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_034 (c : Fin 4) (hr : BaseRetained 34 c.val false) :
    (34,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 34 false 0 packetData0089 (candidatePairList false)
    packetPass0089 route0089 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_035 (c : Fin 4) (hr : BaseRetained 35 c.val false) :
    (35,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 35 false 0 packetData0090 (candidatePairList false)
    packetPass0090 route0090 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_036 (c : Fin 4) (hr : BaseRetained 36 c.val false) :
    (36,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 36 false 0 packetData0091 (candidatePairList false)
    packetPass0091 route0091 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_037 (c : Fin 4) (hr : BaseRetained 37 c.val false) :
    (37,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 37 false 0 packetData0092 (candidatePairList false)
    packetPass0092 route0092 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_038 (c : Fin 4) (hr : BaseRetained 38 c.val false) :
    (38,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 38 false 0 packetData0093 (candidatePairList false)
    packetPass0093 route0093 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_039 (c : Fin 4) (hr : BaseRetained 39 c.val false) :
    (39,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 39 false 0 packetData0094 (candidatePairList false)
    packetPass0094 route0094 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_040 (c : Fin 4) (hr : BaseRetained 40 c.val false) :
    (40,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 40 false 0 packetData0095 (candidatePairList false)
    packetPass0095 route0095 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_041 (c : Fin 4) (hr : BaseRetained 41 c.val false) :
    (41,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 41 false 0 packetData0096 (candidatePairList false)
    packetPass0096 route0096 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_042 (c : Fin 4) (hr : BaseRetained 42 c.val false) :
    (42,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 42 false 0 packetData0097 (candidatePairList false)
    packetPass0097 route0097 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_043 (c : Fin 4) (hr : BaseRetained 43 c.val false) :
    (43,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 43 false 0 packetData0098 (candidatePairList false)
    packetPass0098 route0098 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_044 (c : Fin 4) (hr : BaseRetained 44 c.val false) :
    (44,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 44 false 0 packetData0099 (candidatePairList false)
    packetPass0099 route0099 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_045 (c : Fin 4) (hr : BaseRetained 45 c.val false) :
    (45,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 45 false 0 packetData0100 (candidatePairList false)
    packetPass0100 route0100 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_046 (c : Fin 4) (hr : BaseRetained 46 c.val false) :
    (46,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 46 false 0 packetData0101 (candidatePairList false)
    packetPass0101 route0101 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_047 (c : Fin 4) (hr : BaseRetained 47 c.val false) :
    (47,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 47 false 0 packetData0102 (candidatePairList false)
    packetPass0102 route0102 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_048 (c : Fin 4) (hr : BaseRetained 48 c.val false) :
    (48,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 48 false 0 packetData0103 (candidatePairList false)
    packetPass0103 route0103 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_049 (c : Fin 4) (hr : BaseRetained 49 c.val false) :
    (49,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 49 false 0 packetData0104 (candidatePairList false)
    packetPass0104 route0104 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_050 (c : Fin 4) (hr : BaseRetained 50 c.val false) :
    (50,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 50 false 0 packetData0105 (candidatePairList false)
    packetPass0105 route0105 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_051 (c : Fin 4) (hr : BaseRetained 51 c.val false) :
    (51,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 51 false 0 packetData0106 (candidatePairList false)
    packetPass0106 route0106 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_052 (c : Fin 4) (hr : BaseRetained 52 c.val false) :
    (52,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 52 false 0 packetData0107 (candidatePairList false)
    packetPass0107 route0107 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_053 (c : Fin 4) (hr : BaseRetained 53 c.val false) :
    (53,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 53 false 0 packetData0108 (candidatePairList false)
    packetPass0108 route0108 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_054 (c : Fin 4) (hr : BaseRetained 54 c.val false) :
    (54,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 54 false 0 packetData0109 (candidatePairList false)
    packetPass0109 route0109 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_055 (c : Fin 4) (hr : BaseRetained 55 c.val false) :
    (55,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 55 false 0 packetData0110 (candidatePairList false)
    packetPass0110 route0110 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_056 (c : Fin 4) (hr : BaseRetained 56 c.val false) :
    (56,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 56 false 0 packetData0111 (candidatePairList false)
    packetPass0111 route0111 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_057 (c : Fin 4) (hr : BaseRetained 57 c.val false) :
    (57,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 57 false 0 packetData0112 (candidatePairList false)
    packetPass0112 route0112 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_058 (c : Fin 4) (hr : BaseRetained 58 c.val false) :
    (58,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 58 false 0 packetData0113 (candidatePairList false)
    packetPass0113 route0113 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_059 (c : Fin 4) (hr : BaseRetained 59 c.val false) :
    (59,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 59 false 0 packetData0114 (candidatePairList false)
    packetPass0114 route0114 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_060 (c : Fin 4) (hr : BaseRetained 60 c.val false) :
    (60,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 60 false 0 packetData0115 (candidatePairList false)
    packetPass0115 route0115 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_061 (c : Fin 4) (hr : BaseRetained 61 c.val false) :
    (61,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 61 false 0 packetData0116 (candidatePairList false)
    packetPass0116 route0116 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_062 (c : Fin 4) (hr : BaseRetained 62 c.val false) :
    (62,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 62 false 0 packetData0117 (candidatePairList false)
    packetPass0117 route0117 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_063 (c : Fin 4) (hr : BaseRetained 63 c.val false) :
    (63,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 63 false 0 packetData0118 (candidatePairList false)
    packetPass0118 route0118 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_064 (c : Fin 4) (hr : BaseRetained 64 c.val false) :
    (64,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 64 false 0 packetData0119 (candidatePairList false)
    packetPass0119 route0119 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_065 (c : Fin 4) (hr : BaseRetained 65 c.val false) :
    (65,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 65 false 0 packetData0120 (candidatePairList false)
    packetPass0120 route0120 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_066 (c : Fin 4) (hr : BaseRetained 66 c.val false) :
    (66,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 66 false 0 packetData0121 (candidatePairList false)
    packetPass0121 route0121 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_067 (c : Fin 4) (hr : BaseRetained 67 c.val false) :
    (67,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 67 false 0 packetData0122 (candidatePairList false)
    packetPass0122 route0122 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_068 (c : Fin 4) (hr : BaseRetained 68 c.val false) :
    (68,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 68 false 0 packetData0123 (candidatePairList false)
    packetPass0123 route0123 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_069 (c : Fin 4) (hr : BaseRetained 69 c.val false) :
    (69,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 69 false 0 packetData0124 (candidatePairList false)
    packetPass0124 route0124 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_070 (c : Fin 4) (hr : BaseRetained 70 c.val false) :
    (70,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 70 false 0 packetData0125 (candidatePairList false)
    packetPass0125 route0125 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_071 (c : Fin 4) (hr : BaseRetained 71 c.val false) :
    (71,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 71 false 0 packetData0126 (candidatePairList false)
    packetPass0126 route0126 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_072 (c : Fin 4) (hr : BaseRetained 72 c.val false) :
    (72,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 72 false 0 packetData0127 (candidatePairList false)
    packetPass0127 route0127 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_073 (c : Fin 4) (hr : BaseRetained 73 c.val false) :
    (73,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 73 false 0 packetData0128 (candidatePairList false)
    packetPass0128 route0128 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_074 (c : Fin 4) (hr : BaseRetained 74 c.val false) :
    (74,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 74 false 0 packetData0129 (candidatePairList false)
    packetPass0129 route0129 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_075 (c : Fin 4) (hr : BaseRetained 75 c.val false) :
    (75,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 75 false 0 packetData0130 (candidatePairList false)
    packetPass0130 route0130 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_076 (c : Fin 4) (hr : BaseRetained 76 c.val false) :
    (76,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 76 false 0 packetData0131 (candidatePairList false)
    packetPass0131 route0131 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_077 (c : Fin 4) (hr : BaseRetained 77 c.val false) :
    (77,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 77 false 0 packetData0132 (candidatePairList false)
    packetPass0132 route0132 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_078 (c : Fin 4) (hr : BaseRetained 78 c.val false) :
    (78,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 78 false 0 packetData0133 (candidatePairList false)
    packetPass0133 route0133 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_079 (c : Fin 4) (hr : BaseRetained 79 c.val false) :
    (79,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 79 false 0 packetData0134 (candidatePairList false)
    packetPass0134 route0134 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_080 (c : Fin 4) (hr : BaseRetained 80 c.val false) :
    (80,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 80 false 0 packetData0135 (candidatePairList false)
    packetPass0135 route0135 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_081 (c : Fin 4) (hr : BaseRetained 81 c.val false) :
    (81,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 81 false 0 packetData0136 (candidatePairList false)
    packetPass0136 route0136 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_082 (c : Fin 4) (hr : BaseRetained 82 c.val false) :
    (82,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 82 false 0 packetData0137 (candidatePairList false)
    packetPass0137 route0137 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_083 (c : Fin 4) (hr : BaseRetained 83 c.val false) :
    (83,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 83 false 0 packetData0138 (candidatePairList false)
    packetPass0138 route0138 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_084 (c : Fin 4) (hr : BaseRetained 84 c.val false) :
    (84,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 84 false 0 packetData0139 (candidatePairList false)
    packetPass0139 route0139 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_085 (c : Fin 4) (hr : BaseRetained 85 c.val false) :
    (85,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 85 false 0 packetData0140 (candidatePairList false)
    packetPass0140 route0140 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_086 (c : Fin 4) (hr : BaseRetained 86 c.val false) :
    (86,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 86 false 0 packetData0141 (candidatePairList false)
    packetPass0141 route0141 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_087 (c : Fin 4) (hr : BaseRetained 87 c.val false) :
    (87,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 87 false 0 packetData0142 (candidatePairList false)
    packetPass0142 route0142 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_088 (c : Fin 4) (hr : BaseRetained 88 c.val false) :
    (88,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 88 false 0 packetData0143 (candidatePairList false)
    packetPass0143 route0143 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_089 (c : Fin 4) (hr : BaseRetained 89 c.val false) :
    (89,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 89 false 0 packetData0144 (candidatePairList false)
    packetPass0144 route0144 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_090 (c : Fin 4) (hr : BaseRetained 90 c.val false) :
    (90,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 90 false 0 packetData0145 (candidatePairList false)
    packetPass0145 route0145 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_091 (c : Fin 4) (hr : BaseRetained 91 c.val false) :
    (91,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 91 false 0 packetData0146 (candidatePairList false)
    packetPass0146 route0146 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_092 (c : Fin 4) (hr : BaseRetained 92 c.val false) :
    (92,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 92 false 0 packetData0147 (candidatePairList false)
    packetPass0147 route0147 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_093 (c : Fin 4) (hr : BaseRetained 93 c.val false) :
    (93,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 93 false 0 packetData0148 (candidatePairList false)
    packetPass0148 route0148 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_094 (c : Fin 4) (hr : BaseRetained 94 c.val false) :
    (94,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 94 false 0 packetData0149 (candidatePairList false)
    packetPass0149 route0149 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_095 (c : Fin 4) (hr : BaseRetained 95 c.val false) :
    (95,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 95 false 0 packetData0150 (candidatePairList false)
    packetPass0150 route0150 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_096 (c : Fin 4) (hr : BaseRetained 96 c.val false) :
    (96,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 96 false 0 packetData0151 (candidatePairList false)
    packetPass0151 route0151 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_097 (c : Fin 4) (hr : BaseRetained 97 c.val false) :
    (97,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 97 false 0 packetData0152 (candidatePairList false)
    packetPass0152 route0152 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_098 (c : Fin 4) (hr : BaseRetained 98 c.val false) :
    (98,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 98 false 0 packetData0153 (candidatePairList false)
    packetPass0153 route0153 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_099 (c : Fin 4) (hr : BaseRetained 99 c.val false) :
    (99,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 99 false 0 packetData0154 (candidatePairList false)
    packetPass0154 route0154 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_100 (c : Fin 4) (hr : BaseRetained 100 c.val false) :
    (100,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 100 false 0 packetData0155 (candidatePairList false)
    packetPass0155 route0155 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_101 (c : Fin 4) (hr : BaseRetained 101 c.val false) :
    (101,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 101 false 0 packetData0156 (candidatePairList false)
    packetPass0156 route0156 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_102 (c : Fin 4) (hr : BaseRetained 102 c.val false) :
    (102,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 102 false 0 packetData0157 (candidatePairList false)
    packetPass0157 route0157 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_103 (c : Fin 4) (hr : BaseRetained 103 c.val false) :
    (103,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 103 false 0 packetData0158 (candidatePairList false)
    packetPass0158 route0158 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_104 (c : Fin 4) (hr : BaseRetained 104 c.val false) :
    (104,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 104 false 0 packetData0159 (candidatePairList false)
    packetPass0159 route0159 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_105 (c : Fin 4) (hr : BaseRetained 105 c.val false) :
    (105,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 105 false 0 packetData0160 (candidatePairList false)
    packetPass0160 route0160 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_106 (c : Fin 4) (hr : BaseRetained 106 c.val false) :
    (106,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 106 false 0 packetData0161 (candidatePairList false)
    packetPass0161 route0161 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_107 (c : Fin 4) (hr : BaseRetained 107 c.val false) :
    (107,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 107 false 0 packetData0162 (candidatePairList false)
    packetPass0162 route0162 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_108 (c : Fin 4) (hr : BaseRetained 108 c.val false) :
    (108,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 108 false 0 packetData0163 (candidatePairList false)
    packetPass0163 route0163 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_109 (c : Fin 4) (hr : BaseRetained 109 c.val false) :
    (109,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 109 false 0 packetData0164 (candidatePairList false)
    packetPass0164 route0164 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_110 (c : Fin 4) (hr : BaseRetained 110 c.val false) :
    (110,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 110 false 0 packetData0165 (candidatePairList false)
    packetPass0165 route0165 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_111 (c : Fin 4) (hr : BaseRetained 111 c.val false) :
    (111,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 111 false 0 packetData0166 (candidatePairList false)
    packetPass0166 route0166 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_112 (c : Fin 4) (hr : BaseRetained 112 c.val false) :
    (112,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 112 false 0 packetData0167 (candidatePairList false)
    packetPass0167 route0167 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_113 (c : Fin 4) (hr : BaseRetained 113 c.val false) :
    (113,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 113 false 0 packetData0168 (candidatePairList false)
    packetPass0168 route0168 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_114 (c : Fin 4) (hr : BaseRetained 114 c.val false) :
    (114,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 114 false 0 packetData0169 (candidatePairList false)
    packetPass0169 route0169 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_115 (c : Fin 4) (hr : BaseRetained 115 c.val false) :
    (115,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 115 false 0 packetData0170 (candidatePairList false)
    packetPass0170 route0170 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_116 (c : Fin 4) (hr : BaseRetained 116 c.val false) :
    (116,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 116 false 0 packetData0171 (candidatePairList false)
    packetPass0171 route0171 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_117 (c : Fin 4) (hr : BaseRetained 117 c.val false) :
    (117,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 117 false 0 packetData0172 (candidatePairList false)
    packetPass0172 route0172 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_118 (c : Fin 4) (hr : BaseRetained 118 c.val false) :
    (118,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 118 false 0 packetData0173 (candidatePairList false)
    packetPass0173 route0173 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_119 (c : Fin 4) (hr : BaseRetained 119 c.val false) :
    (119,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 119 false 0 packetData0174 (candidatePairList false)
    packetPass0174 route0174 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_120 (c : Fin 4) (hr : BaseRetained 120 c.val false) :
    (120,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 120 false 0 packetData0175 (candidatePairList false)
    packetPass0175 route0175 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_121 (c : Fin 4) (hr : BaseRetained 121 c.val false) :
    (121,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 121 false 0 packetData0176 (candidatePairList false)
    packetPass0176 route0176 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_122 (c : Fin 4) (hr : BaseRetained 122 c.val false) :
    (122,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 122 false 0 packetData0177 (candidatePairList false)
    packetPass0177 route0177 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_123 (c : Fin 4) (hr : BaseRetained 123 c.val false) :
    (123,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 123 false 0 packetData0178 (candidatePairList false)
    packetPass0178 route0178 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_124 (c : Fin 4) (hr : BaseRetained 124 c.val false) :
    (124,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 124 false 0 packetData0179 (candidatePairList false)
    packetPass0179 route0179 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_125 (c : Fin 4) (hr : BaseRetained 125 c.val false) :
    (125,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 125 false 0 packetData0180 (candidatePairList false)
    packetPass0180 route0180 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_126 (c : Fin 4) (hr : BaseRetained 126 c.val false) :
    (126,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 126 false 0 packetData0181 (candidatePairList false)
    packetPass0181 route0181 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_127 (c : Fin 4) (hr : BaseRetained 127 c.val false) :
    (127,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 127 false 0 packetData0182 (candidatePairList false)
    packetPass0182 route0182 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_128 (c : Fin 4) (hr : BaseRetained 128 c.val false) :
    (128,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 128 false 0 packetData0000 (candidatePairList false)
    packetPass0000 route0000 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_129 (c : Fin 4) (hr : BaseRetained 129 c.val false) :
    (129,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 129 false 0 packetData0001 (candidatePairList false)
    packetPass0001 route0001 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_130 (c : Fin 4) (hr : BaseRetained 130 c.val false) :
    (130,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 130 false 0 packetData0002 (candidatePairList false)
    packetPass0002 route0002 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_131 (c : Fin 4) (hr : BaseRetained 131 c.val false) :
    (131,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 131 false 0 packetData0003 (candidatePairList false)
    packetPass0003 route0003 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_132 (c : Fin 4) (hr : BaseRetained 132 c.val false) :
    (132,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 132 false 0 packetData0004 (candidatePairList false)
    packetPass0004 route0004 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_133 (c : Fin 4) (hr : BaseRetained 133 c.val false) :
    (133,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 133 false 0 packetData0005 (candidatePairList false)
    packetPass0005 route0005 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_134 (c : Fin 4) (hr : BaseRetained 134 c.val false) :
    (134,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 134 false 0 packetData0006 (candidatePairList false)
    packetPass0006 route0006 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_135 (c : Fin 4) (hr : BaseRetained 135 c.val false) :
    (135,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 135 false 0 packetData0007 (candidatePairList false)
    packetPass0007 route0007 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_136 (c : Fin 32) (hr : BaseRetained 136 c.val false) :
    (136,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 136 false 0 packetData0183 (candidatePairList false)
    packetPass0183 route0183 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_137 (c : Fin 32) (hr : BaseRetained 137 c.val false) :
    (137,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 137 false 0 packetData0184 (candidatePairList false)
    packetPass0184 route0184 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_138 (c : Fin 32) (hr : BaseRetained 138 c.val false) :
    (138,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 138 false 0 packetData0185 (candidatePairList false)
    packetPass0185 route0185 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_139 (c : Fin 32) (hr : BaseRetained 139 c.val false) :
    (139,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 139 false 0 packetData0186 (candidatePairList false)
    packetPass0186 route0186 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_140 (c : Fin 32) (hr : BaseRetained 140 c.val false) :
    (140,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 140 false 0 packetData0187 (candidatePairList false)
    packetPass0187 route0187 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_141 (c : Fin 32) (hr : BaseRetained 141 c.val false) :
    (141,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 141 false 0 packetData0188 (candidatePairList false)
    packetPass0188 route0188 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_142 (c : Fin 32) (hr : BaseRetained 142 c.val false) :
    (142,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 142 false 0 packetData0189 (candidatePairList false)
    packetPass0189 route0189 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_143 (c : Fin 32) (hr : BaseRetained 143 c.val false) :
    (143,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 143 false 0 packetData0190 (candidatePairList false)
    packetPass0190 route0190 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_144 (c : Fin 32) (hr : BaseRetained 144 c.val false) :
    (144,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 144 false 0 packetData0191 (candidatePairList false)
    packetPass0191 route0191 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_145 (c : Fin 32) (hr : BaseRetained 145 c.val false) :
    (145,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 145 false 0 packetData0192 (candidatePairList false)
    packetPass0192 route0192 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_146 (c : Fin 32) (hr : BaseRetained 146 c.val false) :
    (146,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 146 false 0 packetData0193 (candidatePairList false)
    packetPass0193 route0193 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_147 (c : Fin 32) (hr : BaseRetained 147 c.val false) :
    (147,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 147 false 0 packetData0194 (candidatePairList false)
    packetPass0194 route0194 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_148 (c : Fin 32) (hr : BaseRetained 148 c.val false) :
    (148,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 148 false 0 packetData0195 (candidatePairList false)
    packetPass0195 route0195 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_149 (c : Fin 32) (hr : BaseRetained 149 c.val false) :
    (149,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 149 false 0 packetData0196 (candidatePairList false)
    packetPass0196 route0196 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_150 (c : Fin 32) (hr : BaseRetained 150 c.val false) :
    (150,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 150 false 0 packetData0197 (candidatePairList false)
    packetPass0197 route0197 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_151 (c : Fin 32) (hr : BaseRetained 151 c.val false) :
    (151,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 151 false 0 packetData0198 (candidatePairList false)
    packetPass0198 route0198 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_152 (c : Fin 32) (hr : BaseRetained 152 c.val false) :
    (152,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 152 false 0 packetData0199 (candidatePairList false)
    packetPass0199 route0199 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_153 (c : Fin 32) (hr : BaseRetained 153 c.val false) :
    (153,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 153 false 0 packetData0200 (candidatePairList false)
    packetPass0200 route0200 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_154 (c : Fin 32) (hr : BaseRetained 154 c.val false) :
    (154,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 154 false 0 packetData0201 (candidatePairList false)
    packetPass0201 route0201 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_155 (c : Fin 32) (hr : BaseRetained 155 c.val false) :
    (155,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 155 false 0 packetData0202 (candidatePairList false)
    packetPass0202 route0202 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_156 (c : Fin 32) (hr : BaseRetained 156 c.val false) :
    (156,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 156 false 0 packetData0203 (candidatePairList false)
    packetPass0203 route0203 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_157 (c : Fin 32) (hr : BaseRetained 157 c.val false) :
    (157,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 157 false 0 packetData0204 (candidatePairList false)
    packetPass0204 route0204 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_158 (c : Fin 32) (hr : BaseRetained 158 c.val false) :
    (158,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 158 false 0 packetData0205 (candidatePairList false)
    packetPass0205 route0205 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_159 (c : Fin 32) (hr : BaseRetained 159 c.val false) :
    (159,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 159 false 0 packetData0206 (candidatePairList false)
    packetPass0206 route0206 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_160 (c : Fin 32) (hr : BaseRetained 160 c.val false) :
    (160,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 160 false 0 packetData0207 (candidatePairList false)
    packetPass0207 route0207 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_161 (c : Fin 32) (hr : BaseRetained 161 c.val false) :
    (161,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 161 false 0 packetData0208 (candidatePairList false)
    packetPass0208 route0208 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_162 (c : Fin 32) (hr : BaseRetained 162 c.val false) :
    (162,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 162 false 0 packetData0209 (candidatePairList false)
    packetPass0209 route0209 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_163 (c : Fin 32) (hr : BaseRetained 163 c.val false) :
    (163,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 163 false 0 packetData0210 (candidatePairList false)
    packetPass0210 route0210 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_164 (c : Fin 32) (hr : BaseRetained 164 c.val false) :
    (164,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 164 false 0 packetData0211 (candidatePairList false)
    packetPass0211 route0211 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_165 (c : Fin 32) (hr : BaseRetained 165 c.val false) :
    (165,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 165 false 0 packetData0212 (candidatePairList false)
    packetPass0212 route0212 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_166 (c : Fin 32) (hr : BaseRetained 166 c.val false) :
    (166,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 166 false 0 packetData0213 (candidatePairList false)
    packetPass0213 route0213 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_167 (c : Fin 32) (hr : BaseRetained 167 c.val false) :
    (167,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 167 false 0 packetData0214 (candidatePairList false)
    packetPass0214 route0214 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_168 (c : Fin 32) (hr : BaseRetained 168 c.val false) :
    (168,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 168 false 0 packetData0215 (candidatePairList false)
    packetPass0215 route0215 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_169 (c : Fin 32) (hr : BaseRetained 169 c.val false) :
    (169,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 169 false 0 packetData0216 (candidatePairList false)
    packetPass0216 route0216 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_170 (c : Fin 32) (hr : BaseRetained 170 c.val false) :
    (170,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 170 false 0 packetData0217 (candidatePairList false)
    packetPass0217 route0217 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_171 (c : Fin 32) (hr : BaseRetained 171 c.val false) :
    (171,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 171 false 0 packetData0218 (candidatePairList false)
    packetPass0218 route0218 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_172 (c : Fin 32) (hr : BaseRetained 172 c.val false) :
    (172,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 172 false 0 packetData0219 (candidatePairList false)
    packetPass0219 route0219 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_173 (c : Fin 32) (hr : BaseRetained 173 c.val false) :
    (173,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 173 false 0 packetData0220 (candidatePairList false)
    packetPass0220 route0220 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_174 (c : Fin 32) (hr : BaseRetained 174 c.val false) :
    (174,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 174 false 0 packetData0221 (candidatePairList false)
    packetPass0221 route0221 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_175 (c : Fin 32) (hr : BaseRetained 175 c.val false) :
    (175,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 175 false 0 packetData0222 (candidatePairList false)
    packetPass0222 route0222 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_176 (c : Fin 32) (hr : BaseRetained 176 c.val false) :
    (176,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 176 false 0 packetData0223 (candidatePairList false)
    packetPass0223 route0223 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_177 (c : Fin 32) (hr : BaseRetained 177 c.val false) :
    (177,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 177 false 0 packetData0224 (candidatePairList false)
    packetPass0224 route0224 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_178 (c : Fin 32) (hr : BaseRetained 178 c.val false) :
    (178,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 178 false 0 packetData0225 (candidatePairList false)
    packetPass0225 route0225 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_179 (c : Fin 32) (hr : BaseRetained 179 c.val false) :
    (179,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 179 false 0 packetData0226 (candidatePairList false)
    packetPass0226 route0226 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_180 (c : Fin 32) (hr : BaseRetained 180 c.val false) :
    (180,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 180 false 0 packetData0227 (candidatePairList false)
    packetPass0227 route0227 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_181 (c : Fin 32) (hr : BaseRetained 181 c.val false) :
    (181,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 181 false 0 packetData0228 (candidatePairList false)
    packetPass0228 route0228 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_182 (c : Fin 32) (hr : BaseRetained 182 c.val false) :
    (182,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 182 false 0 packetData0229 (candidatePairList false)
    packetPass0229 route0229 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_183 (c : Fin 32) (hr : BaseRetained 183 c.val false) :
    (183,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 183 false 0 packetData0230 (candidatePairList false)
    packetPass0230 route0230 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_184 (c : Fin 32) (hr : BaseRetained 184 c.val false) :
    (184,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 184 false 0 packetData0231 (candidatePairList false)
    packetPass0231 route0231 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_185 (c : Fin 32) (hr : BaseRetained 185 c.val false) :
    (185,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 185 false 0 packetData0232 (candidatePairList false)
    packetPass0232 route0232 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_186 (c : Fin 32) (hr : BaseRetained 186 c.val false) :
    (186,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 186 false 0 packetData0233 (candidatePairList false)
    packetPass0233 route0233 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_187 (c : Fin 32) (hr : BaseRetained 187 c.val false) :
    (187,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 187 false 0 packetData0234 (candidatePairList false)
    packetPass0234 route0234 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_188 (c : Fin 32) (hr : BaseRetained 188 c.val false) :
    (188,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 188 false 0 packetData0235 (candidatePairList false)
    packetPass0235 route0235 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_189 (c : Fin 32) (hr : BaseRetained 189 c.val false) :
    (189,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 189 false 0 packetData0236 (candidatePairList false)
    packetPass0236 route0236 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_190 (c : Fin 32) (hr : BaseRetained 190 c.val false) :
    (190,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 190 false 0 packetData0237 (candidatePairList false)
    packetPass0237 route0237 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_191 (c : Fin 32) (hr : BaseRetained 191 c.val false) :
    (191,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 191 false 0 packetData0238 (candidatePairList false)
    packetPass0238 route0238 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_192 (c : Fin 32) (hr : BaseRetained 192 c.val false) :
    (192,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 192 false 0 packetData0239 (candidatePairList false)
    packetPass0239 route0239 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_193 (c : Fin 32) (hr : BaseRetained 193 c.val false) :
    (193,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 193 false 0 packetData0240 (candidatePairList false)
    packetPass0240 route0240 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_194 (c : Fin 32) (hr : BaseRetained 194 c.val false) :
    (194,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 194 false 0 packetData0241 (candidatePairList false)
    packetPass0241 route0241 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_195 (c : Fin 32) (hr : BaseRetained 195 c.val false) :
    (195,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 195 false 0 packetData0242 (candidatePairList false)
    packetPass0242 route0242 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_196 (c : Fin 32) (hr : BaseRetained 196 c.val false) :
    (196,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 196 false 0 packetData0243 (candidatePairList false)
    packetPass0243 route0243 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_197 (c : Fin 32) (hr : BaseRetained 197 c.val false) :
    (197,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 197 false 0 packetData0244 (candidatePairList false)
    packetPass0244 route0244 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_198 (c : Fin 32) (hr : BaseRetained 198 c.val false) :
    (198,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 198 false 0 packetData0245 (candidatePairList false)
    packetPass0245 route0245 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_199 (c : Fin 32) (hr : BaseRetained 199 c.val false) :
    (199,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 199 false 0 packetData0246 (candidatePairList false)
    packetPass0246 route0246 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_200 (c : Fin 32) (hr : BaseRetained 200 c.val false) :
    (200,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 200 false 0 packetData0247 (candidatePairList false)
    packetPass0247 route0247 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_201 (c : Fin 32) (hr : BaseRetained 201 c.val false) :
    (201,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 201 false 0 packetData0248 (candidatePairList false)
    packetPass0248 route0248 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_202 (c : Fin 32) (hr : BaseRetained 202 c.val false) :
    (202,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 202 false 0 packetData0249 (candidatePairList false)
    packetPass0249 route0249 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_203 (c : Fin 32) (hr : BaseRetained 203 c.val false) :
    (203,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 203 false 0 packetData0250 (candidatePairList false)
    packetPass0250 route0250 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_204 (c : Fin 32) (hr : BaseRetained 204 c.val false) :
    (204,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 204 false 0 packetData0008 (candidatePairList false)
    packetPass0008 route0008 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_205 (c : Fin 32) (hr : BaseRetained 205 c.val false) :
    (205,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 205 false 0 packetData0009 (candidatePairList false)
    packetPass0009 route0009 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_206 (c : Fin 32) (hr : BaseRetained 206 c.val false) :
    (206,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 206 false 0 packetData0010 (candidatePairList false)
    packetPass0010 route0010 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_207 (c : Fin 32) (hr : BaseRetained 207 c.val false) :
    (207,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 207 false 0 packetData0011 (candidatePairList false)
    packetPass0011 route0011 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_208 (c : Fin 32) (hr : BaseRetained 208 c.val false) :
    (208,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 208 false 0 packetData0251 (candidatePairList false)
    packetPass0251 route0251 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_209 (c : Fin 32) (hr : BaseRetained 209 c.val false) :
    (209,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 209 false 0 packetData0252 (candidatePairList false)
    packetPass0252 route0252 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_210 (c : Fin 32) (hr : BaseRetained 210 c.val false) :
    (210,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 210 false 0 packetData0253 (candidatePairList false)
    packetPass0253 route0253 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_211 (c : Fin 32) (hr : BaseRetained 211 c.val false) :
    (211,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 211 false 0 packetData0254 (candidatePairList false)
    packetPass0254 route0254 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_212 (c : Fin 32) (hr : BaseRetained 212 c.val false) :
    (212,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 212 false 0 packetData0255 (candidatePairList false)
    packetPass0255 route0255 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_213 (c : Fin 32) (hr : BaseRetained 213 c.val false) :
    (213,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 213 false 0 packetData0256 (candidatePairList false)
    packetPass0256 route0256 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_214 (c : Fin 32) (hr : BaseRetained 214 c.val false) :
    (214,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 214 false 0 packetData0257 (candidatePairList false)
    packetPass0257 route0257 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_215 (c : Fin 32) (hr : BaseRetained 215 c.val false) :
    (215,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 215 false 0 packetData0258 (candidatePairList false)
    packetPass0258 route0258 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_216 (c : Fin 32) (hr : BaseRetained 216 c.val false) :
    (216,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 216 false 0 packetData0259 (candidatePairList false)
    packetPass0259 route0259 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_217 (c : Fin 32) (hr : BaseRetained 217 c.val false) :
    (217,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 217 false 0 packetData0260 (candidatePairList false)
    packetPass0260 route0260 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_218 (c : Fin 32) (hr : BaseRetained 218 c.val false) :
    (218,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 218 false 0 packetData0261 (candidatePairList false)
    packetPass0261 route0261 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_219 (c : Fin 32) (hr : BaseRetained 219 c.val false) :
    (219,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 219 false 0 packetData0262 (candidatePairList false)
    packetPass0262 route0262 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_220 (c : Fin 32) (hr : BaseRetained 220 c.val false) :
    (220,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 220 false 0 packetData0263 (candidatePairList false)
    packetPass0263 route0263 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_221 (c : Fin 32) (hr : BaseRetained 221 c.val false) :
    (221,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 221 false 0 packetData0264 (candidatePairList false)
    packetPass0264 route0264 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_222 (c : Fin 32) (hr : BaseRetained 222 c.val false) :
    (222,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 222 false 0 packetData0265 (candidatePairList false)
    packetPass0265 route0265 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_223 (c : Fin 32) (hr : BaseRetained 223 c.val false) :
    (223,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 223 false 0 packetData0266 (candidatePairList false)
    packetPass0266 route0266 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_224 (c : Fin 32) (hr : BaseRetained 224 c.val false) :
    (224,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 224 false 0 packetData0267 (candidatePairList false)
    packetPass0267 route0267 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_225 (c : Fin 32) (hr : BaseRetained 225 c.val false) :
    (225,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 225 false 0 packetData0268 (candidatePairList false)
    packetPass0268 route0268 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_226 (c : Fin 32) (hr : BaseRetained 226 c.val false) :
    (226,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 226 false 0 packetData0269 (candidatePairList false)
    packetPass0269 route0269 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_227 (c : Fin 32) (hr : BaseRetained 227 c.val false) :
    (227,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 227 false 0 packetData0270 (candidatePairList false)
    packetPass0270 route0270 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_228 (c : Fin 32) (hr : BaseRetained 228 c.val false) :
    (228,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 228 false 0 packetData0271 (candidatePairList false)
    packetPass0271 route0271 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_229 (c : Fin 32) (hr : BaseRetained 229 c.val false) :
    (229,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 229 false 0 packetData0272 (candidatePairList false)
    packetPass0272 route0272 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_230 (c : Fin 32) (hr : BaseRetained 230 c.val false) :
    (230,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 230 false 0 packetData0273 (candidatePairList false)
    packetPass0273 route0273 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_231 (c : Fin 32) (hr : BaseRetained 231 c.val false) :
    (231,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 231 false 0 packetData0274 (candidatePairList false)
    packetPass0274 route0274 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_232 (c : Fin 32) (hr : BaseRetained 232 c.val false) :
    (232,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 232 false 0 packetData0275 (candidatePairList false)
    packetPass0275 route0275 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_233 (c : Fin 32) (hr : BaseRetained 233 c.val false) :
    (233,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 233 false 0 packetData0276 (candidatePairList false)
    packetPass0276 route0276 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_234 (c : Fin 32) (hr : BaseRetained 234 c.val false) :
    (234,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 234 false 0 packetData0277 (candidatePairList false)
    packetPass0277 route0277 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_235 (c : Fin 32) (hr : BaseRetained 235 c.val false) :
    (235,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 235 false 0 packetData0278 (candidatePairList false)
    packetPass0278 route0278 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_236 (c : Fin 32) (hr : BaseRetained 236 c.val false) :
    (236,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 236 false 0 packetData0012 (candidatePairList false)
    packetPass0012 route0012 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_237 (c : Fin 32) (hr : BaseRetained 237 c.val false) :
    (237,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 237 false 0 packetData0013 (candidatePairList false)
    packetPass0013 route0013 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_238 (c : Fin 32) (hr : BaseRetained 238 c.val false) :
    (238,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 238 false 0 packetData0014 (candidatePairList false)
    packetPass0014 route0014 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_239 (c : Fin 32) (hr : BaseRetained 239 c.val false) :
    (239,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 239 false 0 packetData0015 (candidatePairList false)
    packetPass0015 route0015 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_240 (c : Fin 32) (hr : BaseRetained 240 c.val false) :
    (240,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 240 false 0 packetData0279 (candidatePairList false)
    packetPass0279 route0279 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_241 (c : Fin 32) (hr : BaseRetained 241 c.val false) :
    (241,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 241 false 0 packetData0280 (candidatePairList false)
    packetPass0280 route0280 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_242 (c : Fin 32) (hr : BaseRetained 242 c.val false) :
    (242,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 242 false 0 packetData0281 (candidatePairList false)
    packetPass0281 route0281 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_243 (c : Fin 32) (hr : BaseRetained 243 c.val false) :
    (243,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 243 false 0 packetData0282 (candidatePairList false)
    packetPass0282 route0282 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_244 (c : Fin 32) (hr : BaseRetained 244 c.val false) :
    (244,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 244 false 0 packetData0283 (candidatePairList false)
    packetPass0283 route0283 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_245 (c : Fin 32) (hr : BaseRetained 245 c.val false) :
    (245,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 245 false 0 packetData0284 (candidatePairList false)
    packetPass0284 route0284 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_246 (c : Fin 32) (hr : BaseRetained 246 c.val false) :
    (246,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 246 false 0 packetData0285 (candidatePairList false)
    packetPass0285 route0285 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_247 (c : Fin 32) (hr : BaseRetained 247 c.val false) :
    (247,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 247 false 0 packetData0286 (candidatePairList false)
    packetPass0286 route0286 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_248 (c : Fin 32) (hr : BaseRetained 248 c.val false) :
    (248,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 248 false 0 packetData0016 (candidatePairList false)
    packetPass0016 route0016 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_249 (c : Fin 32) (hr : BaseRetained 249 c.val false) :
    (249,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 249 false 0 packetData0017 (candidatePairList false)
    packetPass0017 route0017 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_250 (c : Fin 32) (hr : BaseRetained 250 c.val false) :
    (250,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 250 false 0 packetData0018 (candidatePairList false)
    packetPass0018 route0018 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_251 (c : Fin 32) (hr : BaseRetained 251 c.val false) :
    (251,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 251 false 0 packetData0019 (candidatePairList false)
    packetPass0019 route0019 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_252 (c : Fin 32) (hr : BaseRetained 252 c.val false) :
    (252,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 252 false 0 packetData0287 (candidatePairList false)
    packetPass0287 route0287 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_253 (c : Fin 32) (hr : BaseRetained 253 c.val false) :
    (253,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 253 false 0 packetData0288 (candidatePairList false)
    packetPass0288 route0288 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_254 (c : Fin 32) (hr : BaseRetained 254 c.val false) :
    (254,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 254 false 0 packetData0289 (candidatePairList false)
    packetPass0289 route0289 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_255 (c : Fin 32) (hr : BaseRetained 255 c.val false) :
    (255,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 255 false 0 packetData0290 (candidatePairList false)
    packetPass0290 route0290 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_256 (c : Fin 32) (hr : BaseRetained 256 c.val false) :
    (256,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 256 false 0 packetData0291 (candidatePairList false)
    packetPass0291 route0291 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_257 (c : Fin 32) (hr : BaseRetained 257 c.val false) :
    (257,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 257 false 0 packetData0292 (candidatePairList false)
    packetPass0292 route0292 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_258 (c : Fin 32) (hr : BaseRetained 258 c.val false) :
    (258,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 258 false 0 packetData0293 (candidatePairList false)
    packetPass0293 route0293 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_259 (c : Fin 32) (hr : BaseRetained 259 c.val false) :
    (259,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 259 false 0 packetData0294 (candidatePairList false)
    packetPass0294 route0294 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_260 (c : Fin 32) (hr : BaseRetained 260 c.val false) :
    (260,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 260 false 0 packetData0295 (candidatePairList false)
    packetPass0295 route0295 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_261 (c : Fin 32) (hr : BaseRetained 261 c.val false) :
    (261,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 261 false 0 packetData0296 (candidatePairList false)
    packetPass0296 route0296 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_262 (c : Fin 32) (hr : BaseRetained 262 c.val false) :
    (262,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 262 false 0 packetData0297 (candidatePairList false)
    packetPass0297 route0297 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_263 (c : Fin 32) (hr : BaseRetained 263 c.val false) :
    (263,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 263 false 0 packetData0298 (candidatePairList false)
    packetPass0298 route0298 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_264 (c : Fin 32) (hr : BaseRetained 264 c.val false) :
    (264,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 264 false 0 packetData0299 (candidatePairList false)
    packetPass0299 route0299 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_265 (c : Fin 32) (hr : BaseRetained 265 c.val false) :
    (265,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 265 false 0 packetData0300 (candidatePairList false)
    packetPass0300 route0300 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_266 (c : Fin 32) (hr : BaseRetained 266 c.val false) :
    (266,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 266 false 0 packetData0301 (candidatePairList false)
    packetPass0301 route0301 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_267 (c : Fin 32) (hr : BaseRetained 267 c.val false) :
    (267,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 267 false 0 packetData0302 (candidatePairList false)
    packetPass0302 route0302 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_268 (c : Fin 32) (hr : BaseRetained 268 c.val false) :
    (268,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 268 false 0 packetData0303 (candidatePairList false)
    packetPass0303 route0303 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_269 (c : Fin 32) (hr : BaseRetained 269 c.val false) :
    (269,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 269 false 0 packetData0304 (candidatePairList false)
    packetPass0304 route0304 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_270 (c : Fin 32) (hr : BaseRetained 270 c.val false) :
    (270,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 270 false 0 packetData0305 (candidatePairList false)
    packetPass0305 route0305 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_271 (c : Fin 32) (hr : BaseRetained 271 c.val false) :
    (271,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 271 false 0 packetData0306 (candidatePairList false)
    packetPass0306 route0306 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_272 (c : Fin 32) (hr : BaseRetained 272 c.val false) :
    (272,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 272 false 0 packetData0307 (candidatePairList false)
    packetPass0307 route0307 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_273 (c : Fin 32) (hr : BaseRetained 273 c.val false) :
    (273,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 273 false 0 packetData0308 (candidatePairList false)
    packetPass0308 route0308 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_274 (c : Fin 32) (hr : BaseRetained 274 c.val false) :
    (274,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 274 false 0 packetData0309 (candidatePairList false)
    packetPass0309 route0309 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_275 (c : Fin 32) (hr : BaseRetained 275 c.val false) :
    (275,c.val) ∈ candidatePairList false := by
  have h := packet_retained_route 275 false 0 packetData0310 (candidatePairList false)
    packetPass0310 route0310 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_276 (c : Fin 512) (hr : BaseRetained 276 c.val false) :
    (276,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 276 (p.val*64) (packets_0_276 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0311
    · exact route0312
    · exact route0313
    · exact route0314
    · exact route0315
    · exact route0316
    · exact route0317
    · exact route0318
  have hi : c.val%64 < (packets_0_276 p).size := by rw [packets_size_0_276]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 276 false (p.val*64) (packets_0_276 p) (candidatePairList false)
    (packets_pass_0_276 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_277 (c : Fin 512) (hr : BaseRetained 277 c.val false) :
    (277,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 277 (p.val*64) (packets_0_277 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0319
    · exact route0320
    · exact route0321
    · exact route0322
    · exact route0323
    · exact route0324
    · exact route0325
    · exact route0326
  have hi : c.val%64 < (packets_0_277 p).size := by rw [packets_size_0_277]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 277 false (p.val*64) (packets_0_277 p) (candidatePairList false)
    (packets_pass_0_277 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_278 (c : Fin 512) (hr : BaseRetained 278 c.val false) :
    (278,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 278 (p.val*64) (packets_0_278 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0327
    · exact route0328
    · exact route0329
    · exact route0330
    · exact route0331
    · exact route0332
    · exact route0333
    · exact route0334
  have hi : c.val%64 < (packets_0_278 p).size := by rw [packets_size_0_278]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 278 false (p.val*64) (packets_0_278 p) (candidatePairList false)
    (packets_pass_0_278 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_279 (c : Fin 512) (hr : BaseRetained 279 c.val false) :
    (279,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 279 (p.val*64) (packets_0_279 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0335
    · exact route0336
    · exact route0337
    · exact route0338
    · exact route0339
    · exact route0340
    · exact route0341
    · exact route0342
  have hi : c.val%64 < (packets_0_279 p).size := by rw [packets_size_0_279]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 279 false (p.val*64) (packets_0_279 p) (candidatePairList false)
    (packets_pass_0_279 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_280 (c : Fin 512) (hr : BaseRetained 280 c.val false) :
    (280,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 280 (p.val*64) (packets_0_280 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0343
    · exact route0344
    · exact route0345
    · exact route0346
    · exact route0347
    · exact route0348
    · exact route0349
    · exact route0350
  have hi : c.val%64 < (packets_0_280 p).size := by rw [packets_size_0_280]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 280 false (p.val*64) (packets_0_280 p) (candidatePairList false)
    (packets_pass_0_280 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_281 (c : Fin 512) (hr : BaseRetained 281 c.val false) :
    (281,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 281 (p.val*64) (packets_0_281 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0351
    · exact route0352
    · exact route0353
    · exact route0354
    · exact route0355
    · exact route0356
    · exact route0357
    · exact route0358
  have hi : c.val%64 < (packets_0_281 p).size := by rw [packets_size_0_281]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 281 false (p.val*64) (packets_0_281 p) (candidatePairList false)
    (packets_pass_0_281 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_282 (c : Fin 512) (hr : BaseRetained 282 c.val false) :
    (282,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 282 (p.val*64) (packets_0_282 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0359
    · exact route0360
    · exact route0361
    · exact route0362
    · exact route0363
    · exact route0364
    · exact route0365
    · exact route0366
  have hi : c.val%64 < (packets_0_282 p).size := by rw [packets_size_0_282]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 282 false (p.val*64) (packets_0_282 p) (candidatePairList false)
    (packets_pass_0_282 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_283 (c : Fin 512) (hr : BaseRetained 283 c.val false) :
    (283,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 283 (p.val*64) (packets_0_283 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0367
    · exact route0368
    · exact route0369
    · exact route0370
    · exact route0371
    · exact route0372
    · exact route0373
    · exact route0374
  have hi : c.val%64 < (packets_0_283 p).size := by rw [packets_size_0_283]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 283 false (p.val*64) (packets_0_283 p) (candidatePairList false)
    (packets_pass_0_283 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_284 (c : Fin 512) (hr : BaseRetained 284 c.val false) :
    (284,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 284 (p.val*64) (packets_0_284 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0375
    · exact route0376
    · exact route0377
    · exact route0378
    · exact route0379
    · exact route0380
    · exact route0381
    · exact route0382
  have hi : c.val%64 < (packets_0_284 p).size := by rw [packets_size_0_284]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 284 false (p.val*64) (packets_0_284 p) (candidatePairList false)
    (packets_pass_0_284 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_285 (c : Fin 512) (hr : BaseRetained 285 c.val false) :
    (285,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 285 (p.val*64) (packets_0_285 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0383
    · exact route0384
    · exact route0385
    · exact route0386
    · exact route0387
    · exact route0388
    · exact route0389
    · exact route0390
  have hi : c.val%64 < (packets_0_285 p).size := by rw [packets_size_0_285]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 285 false (p.val*64) (packets_0_285 p) (candidatePairList false)
    (packets_pass_0_285 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_286 (c : Fin 512) (hr : BaseRetained 286 c.val false) :
    (286,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 286 (p.val*64) (packets_0_286 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0391
    · exact route0392
    · exact route0393
    · exact route0394
    · exact route0395
    · exact route0396
    · exact route0397
    · exact route0398
  have hi : c.val%64 < (packets_0_286 p).size := by rw [packets_size_0_286]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 286 false (p.val*64) (packets_0_286 p) (candidatePairList false)
    (packets_pass_0_286 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_287 (c : Fin 512) (hr : BaseRetained 287 c.val false) :
    (287,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 287 (p.val*64) (packets_0_287 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0399
    · exact route0400
    · exact route0401
    · exact route0402
    · exact route0403
    · exact route0404
    · exact route0405
    · exact route0406
  have hi : c.val%64 < (packets_0_287 p).size := by rw [packets_size_0_287]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 287 false (p.val*64) (packets_0_287 p) (candidatePairList false)
    (packets_pass_0_287 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_288 (c : Fin 512) (hr : BaseRetained 288 c.val false) :
    (288,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 288 (p.val*64) (packets_0_288 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0407
    · exact route0408
    · exact route0409
    · exact route0410
    · exact route0411
    · exact route0412
    · exact route0413
    · exact route0414
  have hi : c.val%64 < (packets_0_288 p).size := by rw [packets_size_0_288]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 288 false (p.val*64) (packets_0_288 p) (candidatePairList false)
    (packets_pass_0_288 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_289 (c : Fin 512) (hr : BaseRetained 289 c.val false) :
    (289,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 289 (p.val*64) (packets_0_289 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0415
    · exact route0416
    · exact route0417
    · exact route0418
    · exact route0419
    · exact route0420
    · exact route0421
    · exact route0422
  have hi : c.val%64 < (packets_0_289 p).size := by rw [packets_size_0_289]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 289 false (p.val*64) (packets_0_289 p) (candidatePairList false)
    (packets_pass_0_289 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_290 (c : Fin 512) (hr : BaseRetained 290 c.val false) :
    (290,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 290 (p.val*64) (packets_0_290 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0423
    · exact route0424
    · exact route0425
    · exact route0426
    · exact route0427
    · exact route0428
    · exact route0429
    · exact route0430
  have hi : c.val%64 < (packets_0_290 p).size := by rw [packets_size_0_290]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 290 false (p.val*64) (packets_0_290 p) (candidatePairList false)
    (packets_pass_0_290 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_291 (c : Fin 512) (hr : BaseRetained 291 c.val false) :
    (291,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 291 (p.val*64) (packets_0_291 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0431
    · exact route0432
    · exact route0433
    · exact route0434
    · exact route0435
    · exact route0436
    · exact route0437
    · exact route0438
  have hi : c.val%64 < (packets_0_291 p).size := by rw [packets_size_0_291]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 291 false (p.val*64) (packets_0_291 p) (candidatePairList false)
    (packets_pass_0_291 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_292 (c : Fin 512) (hr : BaseRetained 292 c.val false) :
    (292,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 292 (p.val*64) (packets_0_292 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0439
    · exact route0440
    · exact route0441
    · exact route0442
    · exact route0443
    · exact route0444
    · exact route0445
    · exact route0446
  have hi : c.val%64 < (packets_0_292 p).size := by rw [packets_size_0_292]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 292 false (p.val*64) (packets_0_292 p) (candidatePairList false)
    (packets_pass_0_292 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_293 (c : Fin 512) (hr : BaseRetained 293 c.val false) :
    (293,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 293 (p.val*64) (packets_0_293 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0447
    · exact route0448
    · exact route0449
    · exact route0450
    · exact route0451
    · exact route0452
    · exact route0453
    · exact route0454
  have hi : c.val%64 < (packets_0_293 p).size := by rw [packets_size_0_293]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 293 false (p.val*64) (packets_0_293 p) (candidatePairList false)
    (packets_pass_0_293 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_294 (c : Fin 512) (hr : BaseRetained 294 c.val false) :
    (294,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 294 (p.val*64) (packets_0_294 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0455
    · exact route0456
    · exact route0457
    · exact route0458
    · exact route0459
    · exact route0460
    · exact route0461
    · exact route0462
  have hi : c.val%64 < (packets_0_294 p).size := by rw [packets_size_0_294]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 294 false (p.val*64) (packets_0_294 p) (candidatePairList false)
    (packets_pass_0_294 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_295 (c : Fin 512) (hr : BaseRetained 295 c.val false) :
    (295,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 295 (p.val*64) (packets_0_295 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0463
    · exact route0464
    · exact route0465
    · exact route0466
    · exact route0467
    · exact route0468
    · exact route0469
    · exact route0470
  have hi : c.val%64 < (packets_0_295 p).size := by rw [packets_size_0_295]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 295 false (p.val*64) (packets_0_295 p) (candidatePairList false)
    (packets_pass_0_295 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_296 (c : Fin 512) (hr : BaseRetained 296 c.val false) :
    (296,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 296 (p.val*64) (packets_0_296 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0471
    · exact route0472
    · exact route0473
    · exact route0474
    · exact route0475
    · exact route0476
    · exact route0477
    · exact route0478
  have hi : c.val%64 < (packets_0_296 p).size := by rw [packets_size_0_296]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 296 false (p.val*64) (packets_0_296 p) (candidatePairList false)
    (packets_pass_0_296 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_297 (c : Fin 512) (hr : BaseRetained 297 c.val false) :
    (297,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 297 (p.val*64) (packets_0_297 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0479
    · exact route0480
    · exact route0481
    · exact route0482
    · exact route0483
    · exact route0484
    · exact route0485
    · exact route0486
  have hi : c.val%64 < (packets_0_297 p).size := by rw [packets_size_0_297]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 297 false (p.val*64) (packets_0_297 p) (candidatePairList false)
    (packets_pass_0_297 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_298 (c : Fin 512) (hr : BaseRetained 298 c.val false) :
    (298,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 298 (p.val*64) (packets_0_298 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0487
    · exact route0488
    · exact route0489
    · exact route0490
    · exact route0491
    · exact route0492
    · exact route0493
    · exact route0494
  have hi : c.val%64 < (packets_0_298 p).size := by rw [packets_size_0_298]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 298 false (p.val*64) (packets_0_298 p) (candidatePairList false)
    (packets_pass_0_298 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_299 (c : Fin 512) (hr : BaseRetained 299 c.val false) :
    (299,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 299 (p.val*64) (packets_0_299 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0495
    · exact route0496
    · exact route0497
    · exact route0498
    · exact route0499
    · exact route0500
    · exact route0501
    · exact route0502
  have hi : c.val%64 < (packets_0_299 p).size := by rw [packets_size_0_299]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 299 false (p.val*64) (packets_0_299 p) (candidatePairList false)
    (packets_pass_0_299 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_300 (c : Fin 512) (hr : BaseRetained 300 c.val false) :
    (300,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 300 (p.val*64) (packets_0_300 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0503
    · exact route0504
    · exact route0505
    · exact route0506
    · exact route0507
    · exact route0508
    · exact route0509
    · exact route0510
  have hi : c.val%64 < (packets_0_300 p).size := by rw [packets_size_0_300]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 300 false (p.val*64) (packets_0_300 p) (candidatePairList false)
    (packets_pass_0_300 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_301 (c : Fin 512) (hr : BaseRetained 301 c.val false) :
    (301,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 301 (p.val*64) (packets_0_301 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0511
    · exact route0512
    · exact route0513
    · exact route0514
    · exact route0515
    · exact route0516
    · exact route0517
    · exact route0518
  have hi : c.val%64 < (packets_0_301 p).size := by rw [packets_size_0_301]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 301 false (p.val*64) (packets_0_301 p) (candidatePairList false)
    (packets_pass_0_301 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_302 (c : Fin 512) (hr : BaseRetained 302 c.val false) :
    (302,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 302 (p.val*64) (packets_0_302 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0519
    · exact route0520
    · exact route0521
    · exact route0522
    · exact route0523
    · exact route0524
    · exact route0525
    · exact route0526
  have hi : c.val%64 < (packets_0_302 p).size := by rw [packets_size_0_302]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 302 false (p.val*64) (packets_0_302 p) (candidatePairList false)
    (packets_pass_0_302 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_303 (c : Fin 512) (hr : BaseRetained 303 c.val false) :
    (303,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 303 (p.val*64) (packets_0_303 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0527
    · exact route0528
    · exact route0529
    · exact route0530
    · exact route0531
    · exact route0532
    · exact route0533
    · exact route0534
  have hi : c.val%64 < (packets_0_303 p).size := by rw [packets_size_0_303]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 303 false (p.val*64) (packets_0_303 p) (candidatePairList false)
    (packets_pass_0_303 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_304 (c : Fin 512) (hr : BaseRetained 304 c.val false) :
    (304,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 304 (p.val*64) (packets_0_304 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0535
    · exact route0536
    · exact route0537
    · exact route0538
    · exact route0539
    · exact route0540
    · exact route0541
    · exact route0542
  have hi : c.val%64 < (packets_0_304 p).size := by rw [packets_size_0_304]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 304 false (p.val*64) (packets_0_304 p) (candidatePairList false)
    (packets_pass_0_304 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_305 (c : Fin 512) (hr : BaseRetained 305 c.val false) :
    (305,c.val) ∈ candidatePairList false := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 305 (p.val*64) (packets_0_305 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0543
    · exact route0544
    · exact route0545
    · exact route0546
    · exact route0547
    · exact route0548
    · exact route0549
    · exact route0550
  have hi : c.val%64 < (packets_0_305 p).size := by rw [packets_size_0_305]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 305 false (p.val*64) (packets_0_305 p) (candidatePairList false)
    (packets_pass_0_305 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_306 (c : Fin 16384) (hr : BaseRetained 306 c.val false) :
    (306,c.val) ∈ candidatePairList false := by
  let p : Fin 256 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 256, packetRouteCheck 306 (p.val*64) (packets_0_306 p) (candidatePairList false) = true := by
    intro p
    fin_cases p
    · exact route0551
    · exact route0552
    · exact route0553
    · exact route0554
    · exact route0555
    · exact route0556
    · exact route0557
    · exact route0558
    · exact route0559
    · exact route0560
    · exact route0561
    · exact route0562
    · exact route0563
    · exact route0564
    · exact route0565
    · exact route0566
    · exact route0567
    · exact route0568
    · exact route0569
    · exact route0570
    · exact route0571
    · exact route0572
    · exact route0573
    · exact route0574
    · exact route0575
    · exact route0576
    · exact route0577
    · exact route0578
    · exact route0579
    · exact route0580
    · exact route0581
    · exact route0582
    · exact route0583
    · exact route0584
    · exact route0585
    · exact route0586
    · exact route0587
    · exact route0588
    · exact route0589
    · exact route0590
    · exact route0591
    · exact route0592
    · exact route0593
    · exact route0594
    · exact route0595
    · exact route0596
    · exact route0597
    · exact route0598
    · exact route0599
    · exact route0600
    · exact route0601
    · exact route0602
    · exact route0603
    · exact route0604
    · exact route0605
    · exact route0606
    · exact route0607
    · exact route0608
    · exact route0609
    · exact route0610
    · exact route0611
    · exact route0612
    · exact route0613
    · exact route0614
    · exact route0615
    · exact route0616
    · exact route0617
    · exact route0618
    · exact route0619
    · exact route0620
    · exact route0621
    · exact route0622
    · exact route0623
    · exact route0624
    · exact route0625
    · exact route0626
    · exact route0627
    · exact route0628
    · exact route0629
    · exact route0630
    · exact route0631
    · exact route0632
    · exact route0633
    · exact route0634
    · exact route0635
    · exact route0636
    · exact route0637
    · exact route0638
    · exact route0639
    · exact route0640
    · exact route0641
    · exact route0642
    · exact route0643
    · exact route0644
    · exact route0645
    · exact route0646
    · exact route0647
    · exact route0648
    · exact route0649
    · exact route0650
    · exact route0651
    · exact route0652
    · exact route0653
    · exact route0654
    · exact route0655
    · exact route0656
    · exact route0657
    · exact route0658
    · exact route0659
    · exact route0660
    · exact route0661
    · exact route0662
    · exact route0663
    · exact route0664
    · exact route0665
    · exact route0666
    · exact route0667
    · exact route0668
    · exact route0669
    · exact route0670
    · exact route0671
    · exact route0672
    · exact route0673
    · exact route0674
    · exact route0675
    · exact route0676
    · exact route0677
    · exact route0678
    · exact route0679
    · exact route0680
    · exact route0681
    · exact route0682
    · exact route0683
    · exact route0684
    · exact route0685
    · exact route0686
    · exact route0687
    · exact route0688
    · exact route0689
    · exact route0690
    · exact route0691
    · exact route0692
    · exact route0693
    · exact route0694
    · exact route0695
    · exact route0696
    · exact route0697
    · exact route0698
    · exact route0699
    · exact route0700
    · exact route0701
    · exact route0702
    · exact route0703
    · exact route0704
    · exact route0705
    · exact route0706
    · exact route0707
    · exact route0708
    · exact route0709
    · exact route0710
    · exact route0711
    · exact route0712
    · exact route0713
    · exact route0714
    · exact route0715
    · exact route0716
    · exact route0717
    · exact route0718
    · exact route0719
    · exact route0720
    · exact route0721
    · exact route0722
    · exact route0723
    · exact route0724
    · exact route0725
    · exact route0726
    · exact route0727
    · exact route0728
    · exact route0729
    · exact route0730
    · exact route0731
    · exact route0732
    · exact route0733
    · exact route0734
    · exact route0735
    · exact route0736
    · exact route0737
    · exact route0738
    · exact route0739
    · exact route0740
    · exact route0741
    · exact route0742
    · exact route0743
    · exact route0744
    · exact route0745
    · exact route0746
    · exact route0747
    · exact route0748
    · exact route0749
    · exact route0750
    · exact route0751
    · exact route0752
    · exact route0753
    · exact route0754
    · exact route0755
    · exact route0756
    · exact route0757
    · exact route0758
    · exact route0759
    · exact route0760
    · exact route0761
    · exact route0762
    · exact route0763
    · exact route0764
    · exact route0765
    · exact route0766
    · exact route0767
    · exact route0768
    · exact route0769
    · exact route0770
    · exact route0771
    · exact route0772
    · exact route0773
    · exact route0774
    · exact route0775
    · exact route0776
    · exact route0777
    · exact route0778
    · exact route0779
    · exact route0780
    · exact route0781
    · exact route0782
    · exact route0783
    · exact route0784
    · exact route0785
    · exact route0786
    · exact route0787
    · exact route0788
    · exact route0789
    · exact route0790
    · exact route0791
    · exact route0792
    · exact route0793
    · exact route0794
    · exact route0795
    · exact route0796
    · exact route0797
    · exact route0798
    · exact route0799
    · exact route0800
    · exact route0801
    · exact route0802
    · exact route0803
    · exact route0804
    · exact route0805
    · exact route0806
  have hi : c.val%64 < (packets_0_306 p).size := by rw [packets_size_0_306]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 306 false (p.val*64) (packets_0_306 p) (candidatePairList false)
    (packets_pass_0_306 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_false_complete (c : InputCode) (hr : BaseRetained c.1 c.2.val false) :
    (c.1.val,c.2.val) ∈ candidatePairList false := by
  rcases c with ⟨s,c⟩
  fin_cases s
  · exact retained_false_000 c hr
  · exact retained_false_001 c hr
  · exact retained_false_002 c hr
  · exact retained_false_003 c hr
  · exact retained_false_004 c hr
  · exact retained_false_005 c hr
  · exact retained_false_006 c hr
  · exact retained_false_007 c hr
  · exact retained_false_008 c hr
  · exact retained_false_009 c hr
  · exact retained_false_010 c hr
  · exact retained_false_011 c hr
  · exact retained_false_012 c hr
  · exact retained_false_013 c hr
  · exact retained_false_014 c hr
  · exact retained_false_015 c hr
  · exact retained_false_016 c hr
  · exact retained_false_017 c hr
  · exact retained_false_018 c hr
  · exact retained_false_019 c hr
  · exact retained_false_020 c hr
  · exact retained_false_021 c hr
  · exact retained_false_022 c hr
  · exact retained_false_023 c hr
  · exact retained_false_024 c hr
  · exact retained_false_025 c hr
  · exact retained_false_026 c hr
  · exact retained_false_027 c hr
  · exact retained_false_028 c hr
  · exact retained_false_029 c hr
  · exact retained_false_030 c hr
  · exact retained_false_031 c hr
  · exact retained_false_032 c hr
  · exact retained_false_033 c hr
  · exact retained_false_034 c hr
  · exact retained_false_035 c hr
  · exact retained_false_036 c hr
  · exact retained_false_037 c hr
  · exact retained_false_038 c hr
  · exact retained_false_039 c hr
  · exact retained_false_040 c hr
  · exact retained_false_041 c hr
  · exact retained_false_042 c hr
  · exact retained_false_043 c hr
  · exact retained_false_044 c hr
  · exact retained_false_045 c hr
  · exact retained_false_046 c hr
  · exact retained_false_047 c hr
  · exact retained_false_048 c hr
  · exact retained_false_049 c hr
  · exact retained_false_050 c hr
  · exact retained_false_051 c hr
  · exact retained_false_052 c hr
  · exact retained_false_053 c hr
  · exact retained_false_054 c hr
  · exact retained_false_055 c hr
  · exact retained_false_056 c hr
  · exact retained_false_057 c hr
  · exact retained_false_058 c hr
  · exact retained_false_059 c hr
  · exact retained_false_060 c hr
  · exact retained_false_061 c hr
  · exact retained_false_062 c hr
  · exact retained_false_063 c hr
  · exact retained_false_064 c hr
  · exact retained_false_065 c hr
  · exact retained_false_066 c hr
  · exact retained_false_067 c hr
  · exact retained_false_068 c hr
  · exact retained_false_069 c hr
  · exact retained_false_070 c hr
  · exact retained_false_071 c hr
  · exact retained_false_072 c hr
  · exact retained_false_073 c hr
  · exact retained_false_074 c hr
  · exact retained_false_075 c hr
  · exact retained_false_076 c hr
  · exact retained_false_077 c hr
  · exact retained_false_078 c hr
  · exact retained_false_079 c hr
  · exact retained_false_080 c hr
  · exact retained_false_081 c hr
  · exact retained_false_082 c hr
  · exact retained_false_083 c hr
  · exact retained_false_084 c hr
  · exact retained_false_085 c hr
  · exact retained_false_086 c hr
  · exact retained_false_087 c hr
  · exact retained_false_088 c hr
  · exact retained_false_089 c hr
  · exact retained_false_090 c hr
  · exact retained_false_091 c hr
  · exact retained_false_092 c hr
  · exact retained_false_093 c hr
  · exact retained_false_094 c hr
  · exact retained_false_095 c hr
  · exact retained_false_096 c hr
  · exact retained_false_097 c hr
  · exact retained_false_098 c hr
  · exact retained_false_099 c hr
  · exact retained_false_100 c hr
  · exact retained_false_101 c hr
  · exact retained_false_102 c hr
  · exact retained_false_103 c hr
  · exact retained_false_104 c hr
  · exact retained_false_105 c hr
  · exact retained_false_106 c hr
  · exact retained_false_107 c hr
  · exact retained_false_108 c hr
  · exact retained_false_109 c hr
  · exact retained_false_110 c hr
  · exact retained_false_111 c hr
  · exact retained_false_112 c hr
  · exact retained_false_113 c hr
  · exact retained_false_114 c hr
  · exact retained_false_115 c hr
  · exact retained_false_116 c hr
  · exact retained_false_117 c hr
  · exact retained_false_118 c hr
  · exact retained_false_119 c hr
  · exact retained_false_120 c hr
  · exact retained_false_121 c hr
  · exact retained_false_122 c hr
  · exact retained_false_123 c hr
  · exact retained_false_124 c hr
  · exact retained_false_125 c hr
  · exact retained_false_126 c hr
  · exact retained_false_127 c hr
  · exact retained_false_128 c hr
  · exact retained_false_129 c hr
  · exact retained_false_130 c hr
  · exact retained_false_131 c hr
  · exact retained_false_132 c hr
  · exact retained_false_133 c hr
  · exact retained_false_134 c hr
  · exact retained_false_135 c hr
  · exact retained_false_136 c hr
  · exact retained_false_137 c hr
  · exact retained_false_138 c hr
  · exact retained_false_139 c hr
  · exact retained_false_140 c hr
  · exact retained_false_141 c hr
  · exact retained_false_142 c hr
  · exact retained_false_143 c hr
  · exact retained_false_144 c hr
  · exact retained_false_145 c hr
  · exact retained_false_146 c hr
  · exact retained_false_147 c hr
  · exact retained_false_148 c hr
  · exact retained_false_149 c hr
  · exact retained_false_150 c hr
  · exact retained_false_151 c hr
  · exact retained_false_152 c hr
  · exact retained_false_153 c hr
  · exact retained_false_154 c hr
  · exact retained_false_155 c hr
  · exact retained_false_156 c hr
  · exact retained_false_157 c hr
  · exact retained_false_158 c hr
  · exact retained_false_159 c hr
  · exact retained_false_160 c hr
  · exact retained_false_161 c hr
  · exact retained_false_162 c hr
  · exact retained_false_163 c hr
  · exact retained_false_164 c hr
  · exact retained_false_165 c hr
  · exact retained_false_166 c hr
  · exact retained_false_167 c hr
  · exact retained_false_168 c hr
  · exact retained_false_169 c hr
  · exact retained_false_170 c hr
  · exact retained_false_171 c hr
  · exact retained_false_172 c hr
  · exact retained_false_173 c hr
  · exact retained_false_174 c hr
  · exact retained_false_175 c hr
  · exact retained_false_176 c hr
  · exact retained_false_177 c hr
  · exact retained_false_178 c hr
  · exact retained_false_179 c hr
  · exact retained_false_180 c hr
  · exact retained_false_181 c hr
  · exact retained_false_182 c hr
  · exact retained_false_183 c hr
  · exact retained_false_184 c hr
  · exact retained_false_185 c hr
  · exact retained_false_186 c hr
  · exact retained_false_187 c hr
  · exact retained_false_188 c hr
  · exact retained_false_189 c hr
  · exact retained_false_190 c hr
  · exact retained_false_191 c hr
  · exact retained_false_192 c hr
  · exact retained_false_193 c hr
  · exact retained_false_194 c hr
  · exact retained_false_195 c hr
  · exact retained_false_196 c hr
  · exact retained_false_197 c hr
  · exact retained_false_198 c hr
  · exact retained_false_199 c hr
  · exact retained_false_200 c hr
  · exact retained_false_201 c hr
  · exact retained_false_202 c hr
  · exact retained_false_203 c hr
  · exact retained_false_204 c hr
  · exact retained_false_205 c hr
  · exact retained_false_206 c hr
  · exact retained_false_207 c hr
  · exact retained_false_208 c hr
  · exact retained_false_209 c hr
  · exact retained_false_210 c hr
  · exact retained_false_211 c hr
  · exact retained_false_212 c hr
  · exact retained_false_213 c hr
  · exact retained_false_214 c hr
  · exact retained_false_215 c hr
  · exact retained_false_216 c hr
  · exact retained_false_217 c hr
  · exact retained_false_218 c hr
  · exact retained_false_219 c hr
  · exact retained_false_220 c hr
  · exact retained_false_221 c hr
  · exact retained_false_222 c hr
  · exact retained_false_223 c hr
  · exact retained_false_224 c hr
  · exact retained_false_225 c hr
  · exact retained_false_226 c hr
  · exact retained_false_227 c hr
  · exact retained_false_228 c hr
  · exact retained_false_229 c hr
  · exact retained_false_230 c hr
  · exact retained_false_231 c hr
  · exact retained_false_232 c hr
  · exact retained_false_233 c hr
  · exact retained_false_234 c hr
  · exact retained_false_235 c hr
  · exact retained_false_236 c hr
  · exact retained_false_237 c hr
  · exact retained_false_238 c hr
  · exact retained_false_239 c hr
  · exact retained_false_240 c hr
  · exact retained_false_241 c hr
  · exact retained_false_242 c hr
  · exact retained_false_243 c hr
  · exact retained_false_244 c hr
  · exact retained_false_245 c hr
  · exact retained_false_246 c hr
  · exact retained_false_247 c hr
  · exact retained_false_248 c hr
  · exact retained_false_249 c hr
  · exact retained_false_250 c hr
  · exact retained_false_251 c hr
  · exact retained_false_252 c hr
  · exact retained_false_253 c hr
  · exact retained_false_254 c hr
  · exact retained_false_255 c hr
  · exact retained_false_256 c hr
  · exact retained_false_257 c hr
  · exact retained_false_258 c hr
  · exact retained_false_259 c hr
  · exact retained_false_260 c hr
  · exact retained_false_261 c hr
  · exact retained_false_262 c hr
  · exact retained_false_263 c hr
  · exact retained_false_264 c hr
  · exact retained_false_265 c hr
  · exact retained_false_266 c hr
  · exact retained_false_267 c hr
  · exact retained_false_268 c hr
  · exact retained_false_269 c hr
  · exact retained_false_270 c hr
  · exact retained_false_271 c hr
  · exact retained_false_272 c hr
  · exact retained_false_273 c hr
  · exact retained_false_274 c hr
  · exact retained_false_275 c hr
  · exact retained_false_276 c hr
  · exact retained_false_277 c hr
  · exact retained_false_278 c hr
  · exact retained_false_279 c hr
  · exact retained_false_280 c hr
  · exact retained_false_281 c hr
  · exact retained_false_282 c hr
  · exact retained_false_283 c hr
  · exact retained_false_284 c hr
  · exact retained_false_285 c hr
  · exact retained_false_286 c hr
  · exact retained_false_287 c hr
  · exact retained_false_288 c hr
  · exact retained_false_289 c hr
  · exact retained_false_290 c hr
  · exact retained_false_291 c hr
  · exact retained_false_292 c hr
  · exact retained_false_293 c hr
  · exact retained_false_294 c hr
  · exact retained_false_295 c hr
  · exact retained_false_296 c hr
  · exact retained_false_297 c hr
  · exact retained_false_298 c hr
  · exact retained_false_299 c hr
  · exact retained_false_300 c hr
  · exact retained_false_301 c hr
  · exact retained_false_302 c hr
  · exact retained_false_303 c hr
  · exact retained_false_304 c hr
  · exact retained_false_305 c hr
  · exact retained_false_306 c hr

end Holant.Certificates.AffineEndpointCounts
