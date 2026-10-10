import Holant.Certificates.AffineEndpoint.BasePackets.Block000
import Holant.Certificates.AffineEndpoint.BasePackets.Block001
import Holant.Certificates.AffineEndpoint.BasePackets.Block003
import Holant.Certificates.AffineEndpoint.BasePackets.Block004
import Holant.Certificates.AffineEndpoint.BasePackets.Block005
import Holant.Certificates.AffineEndpoint.BasePackets.Block006
import Holant.Certificates.AffineEndpoint.BasePackets.Block007
import Holant.Certificates.AffineEndpoint.BasePackets.Block008
import Holant.Certificates.AffineEndpoint.BasePackets.Block009
import Holant.Certificates.AffineEndpoint.BasePackets.Block010
import Holant.Certificates.AffineEndpoint.BasePackets.Block011
import Holant.Certificates.AffineEndpoint.BasePackets.Block012
import Holant.Certificates.AffineEndpoint.BasePackets.Block013
import Holant.Certificates.AffineEndpoint.BasePackets.Block014
import Holant.Certificates.AffineEndpoint.BasePackets.Block015
import Holant.Certificates.AffineEndpoint.BasePackets.Block016
import Holant.Certificates.AffineEndpoint.BasePackets.Block017
import Holant.Certificates.AffineEndpoint.BasePackets.Block018
import Holant.Certificates.AffineEndpoint.BasePackets.Block019
import Holant.Certificates.AffineEndpoint.BasePackets.Block020
import Holant.Certificates.AffineEndpoint.BasePackets.Block021
import Holant.Certificates.AffineEndpoint.BasePackets.Block022
import Holant.Certificates.AffineEndpoint.BasePackets.Block023
import Holant.Certificates.AffineEndpoint.BasePackets.Block024
import Holant.Certificates.AffineEndpoint.BasePackets.Block025
import Holant.Certificates.AffineEndpoint.BasePackets.Block026
import Holant.Certificates.AffineEndpoint.BasePackets.Block027
import Holant.Certificates.AffineEndpoint.BasePackets.Block028
import Holant.Certificates.AffineEndpoint.BasePackets.Block029
import Holant.Certificates.AffineEndpoint.BasePackets.Block030
import Holant.Certificates.AffineEndpoint.BasePackets.Block031
import Holant.Certificates.AffineEndpoint.BasePackets.Block032
import Holant.Certificates.AffineEndpoint.BasePackets.Block033
import Holant.Certificates.AffineEndpoint.BasePackets.Block034
import Holant.Certificates.AffineEndpoint.BasePackets.Block035
import Holant.Certificates.AffineEndpoint.BasePackets.Block036
import Holant.Certificates.AffineEndpoint.BasePackets.Block037
import Holant.Certificates.AffineEndpoint.BasePackets.Block038
import Holant.Certificates.AffineEndpoint.BasePackets.Block039
import Holant.Certificates.AffineEndpoint.BasePackets.Block040
import Holant.Certificates.AffineEndpoint.BasePackets.Block041
import Holant.Certificates.AffineEndpoint.BasePackets.Block042
import Holant.Certificates.AffineEndpoint.BasePackets.Block043
import Holant.Certificates.AffineEndpoint.BasePackets.Block044
import Holant.Certificates.AffineEndpoint.BasePackets.Block045
import Holant.Certificates.AffineEndpoint.BasePackets.Block046
import Holant.Certificates.AffineEndpoint.BasePackets.Block047
import Holant.Certificates.AffineEndpoint.BasePackets.Block048
import Holant.Certificates.AffineEndpoint.BasePackets.Block049
import Holant.Certificates.AffineEndpoint.BasePackets.Block050
import Holant.Certificates.AffineEndpoint.PacketCoverage
import Holant.Certificates.AffineEndpoint.BaseTransform
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
open SupportCatalog
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false
 theorem covered_0_000 (c : Fin 1) : ∃w,BaseWitnessCheck 0 c.val false w := by
  refine ⟨packetData0055.getD c.val 0,?_⟩
  have h := packetCheck_sound 0 false 0 packetData0055 packetPass0055 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_001 (c : Fin 1) : ∃w,BaseWitnessCheck 1 c.val false w := by
  refine ⟨packetData0056.getD c.val 0,?_⟩
  have h := packetCheck_sound 1 false 0 packetData0056 packetPass0056 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_002 (c : Fin 1) : ∃w,BaseWitnessCheck 2 c.val false w := by
  refine ⟨packetData0057.getD c.val 0,?_⟩
  have h := packetCheck_sound 2 false 0 packetData0057 packetPass0057 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_003 (c : Fin 1) : ∃w,BaseWitnessCheck 3 c.val false w := by
  refine ⟨packetData0058.getD c.val 0,?_⟩
  have h := packetCheck_sound 3 false 0 packetData0058 packetPass0058 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_004 (c : Fin 1) : ∃w,BaseWitnessCheck 4 c.val false w := by
  refine ⟨packetData0059.getD c.val 0,?_⟩
  have h := packetCheck_sound 4 false 0 packetData0059 packetPass0059 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_005 (c : Fin 1) : ∃w,BaseWitnessCheck 5 c.val false w := by
  refine ⟨packetData0060.getD c.val 0,?_⟩
  have h := packetCheck_sound 5 false 0 packetData0060 packetPass0060 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_006 (c : Fin 1) : ∃w,BaseWitnessCheck 6 c.val false w := by
  refine ⟨packetData0061.getD c.val 0,?_⟩
  have h := packetCheck_sound 6 false 0 packetData0061 packetPass0061 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_007 (c : Fin 1) : ∃w,BaseWitnessCheck 7 c.val false w := by
  refine ⟨packetData0062.getD c.val 0,?_⟩
  have h := packetCheck_sound 7 false 0 packetData0062 packetPass0062 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_008 (c : Fin 1) : ∃w,BaseWitnessCheck 8 c.val false w := by
  refine ⟨packetData0063.getD c.val 0,?_⟩
  have h := packetCheck_sound 8 false 0 packetData0063 packetPass0063 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_009 (c : Fin 1) : ∃w,BaseWitnessCheck 9 c.val false w := by
  refine ⟨packetData0064.getD c.val 0,?_⟩
  have h := packetCheck_sound 9 false 0 packetData0064 packetPass0064 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_010 (c : Fin 1) : ∃w,BaseWitnessCheck 10 c.val false w := by
  refine ⟨packetData0065.getD c.val 0,?_⟩
  have h := packetCheck_sound 10 false 0 packetData0065 packetPass0065 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_011 (c : Fin 1) : ∃w,BaseWitnessCheck 11 c.val false w := by
  refine ⟨packetData0066.getD c.val 0,?_⟩
  have h := packetCheck_sound 11 false 0 packetData0066 packetPass0066 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_012 (c : Fin 1) : ∃w,BaseWitnessCheck 12 c.val false w := by
  refine ⟨packetData0067.getD c.val 0,?_⟩
  have h := packetCheck_sound 12 false 0 packetData0067 packetPass0067 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_013 (c : Fin 1) : ∃w,BaseWitnessCheck 13 c.val false w := by
  refine ⟨packetData0068.getD c.val 0,?_⟩
  have h := packetCheck_sound 13 false 0 packetData0068 packetPass0068 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_014 (c : Fin 1) : ∃w,BaseWitnessCheck 14 c.val false w := by
  refine ⟨packetData0069.getD c.val 0,?_⟩
  have h := packetCheck_sound 14 false 0 packetData0069 packetPass0069 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_015 (c : Fin 1) : ∃w,BaseWitnessCheck 15 c.val false w := by
  refine ⟨packetData0070.getD c.val 0,?_⟩
  have h := packetCheck_sound 15 false 0 packetData0070 packetPass0070 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_016 (c : Fin 4) : ∃w,BaseWitnessCheck 16 c.val false w := by
  refine ⟨packetData0071.getD c.val 0,?_⟩
  have h := packetCheck_sound 16 false 0 packetData0071 packetPass0071 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_017 (c : Fin 4) : ∃w,BaseWitnessCheck 17 c.val false w := by
  refine ⟨packetData0072.getD c.val 0,?_⟩
  have h := packetCheck_sound 17 false 0 packetData0072 packetPass0072 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_018 (c : Fin 4) : ∃w,BaseWitnessCheck 18 c.val false w := by
  refine ⟨packetData0073.getD c.val 0,?_⟩
  have h := packetCheck_sound 18 false 0 packetData0073 packetPass0073 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_019 (c : Fin 4) : ∃w,BaseWitnessCheck 19 c.val false w := by
  refine ⟨packetData0074.getD c.val 0,?_⟩
  have h := packetCheck_sound 19 false 0 packetData0074 packetPass0074 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_020 (c : Fin 4) : ∃w,BaseWitnessCheck 20 c.val false w := by
  refine ⟨packetData0075.getD c.val 0,?_⟩
  have h := packetCheck_sound 20 false 0 packetData0075 packetPass0075 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_021 (c : Fin 4) : ∃w,BaseWitnessCheck 21 c.val false w := by
  refine ⟨packetData0076.getD c.val 0,?_⟩
  have h := packetCheck_sound 21 false 0 packetData0076 packetPass0076 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_022 (c : Fin 4) : ∃w,BaseWitnessCheck 22 c.val false w := by
  refine ⟨packetData0077.getD c.val 0,?_⟩
  have h := packetCheck_sound 22 false 0 packetData0077 packetPass0077 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_023 (c : Fin 4) : ∃w,BaseWitnessCheck 23 c.val false w := by
  refine ⟨packetData0078.getD c.val 0,?_⟩
  have h := packetCheck_sound 23 false 0 packetData0078 packetPass0078 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_024 (c : Fin 4) : ∃w,BaseWitnessCheck 24 c.val false w := by
  refine ⟨packetData0079.getD c.val 0,?_⟩
  have h := packetCheck_sound 24 false 0 packetData0079 packetPass0079 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_025 (c : Fin 4) : ∃w,BaseWitnessCheck 25 c.val false w := by
  refine ⟨packetData0080.getD c.val 0,?_⟩
  have h := packetCheck_sound 25 false 0 packetData0080 packetPass0080 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_026 (c : Fin 4) : ∃w,BaseWitnessCheck 26 c.val false w := by
  refine ⟨packetData0081.getD c.val 0,?_⟩
  have h := packetCheck_sound 26 false 0 packetData0081 packetPass0081 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_027 (c : Fin 4) : ∃w,BaseWitnessCheck 27 c.val false w := by
  refine ⟨packetData0082.getD c.val 0,?_⟩
  have h := packetCheck_sound 27 false 0 packetData0082 packetPass0082 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_028 (c : Fin 4) : ∃w,BaseWitnessCheck 28 c.val false w := by
  refine ⟨packetData0083.getD c.val 0,?_⟩
  have h := packetCheck_sound 28 false 0 packetData0083 packetPass0083 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_029 (c : Fin 4) : ∃w,BaseWitnessCheck 29 c.val false w := by
  refine ⟨packetData0084.getD c.val 0,?_⟩
  have h := packetCheck_sound 29 false 0 packetData0084 packetPass0084 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_030 (c : Fin 4) : ∃w,BaseWitnessCheck 30 c.val false w := by
  refine ⟨packetData0085.getD c.val 0,?_⟩
  have h := packetCheck_sound 30 false 0 packetData0085 packetPass0085 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_031 (c : Fin 4) : ∃w,BaseWitnessCheck 31 c.val false w := by
  refine ⟨packetData0086.getD c.val 0,?_⟩
  have h := packetCheck_sound 31 false 0 packetData0086 packetPass0086 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_032 (c : Fin 4) : ∃w,BaseWitnessCheck 32 c.val false w := by
  refine ⟨packetData0087.getD c.val 0,?_⟩
  have h := packetCheck_sound 32 false 0 packetData0087 packetPass0087 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_033 (c : Fin 4) : ∃w,BaseWitnessCheck 33 c.val false w := by
  refine ⟨packetData0088.getD c.val 0,?_⟩
  have h := packetCheck_sound 33 false 0 packetData0088 packetPass0088 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_034 (c : Fin 4) : ∃w,BaseWitnessCheck 34 c.val false w := by
  refine ⟨packetData0089.getD c.val 0,?_⟩
  have h := packetCheck_sound 34 false 0 packetData0089 packetPass0089 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_035 (c : Fin 4) : ∃w,BaseWitnessCheck 35 c.val false w := by
  refine ⟨packetData0090.getD c.val 0,?_⟩
  have h := packetCheck_sound 35 false 0 packetData0090 packetPass0090 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_036 (c : Fin 4) : ∃w,BaseWitnessCheck 36 c.val false w := by
  refine ⟨packetData0091.getD c.val 0,?_⟩
  have h := packetCheck_sound 36 false 0 packetData0091 packetPass0091 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_037 (c : Fin 4) : ∃w,BaseWitnessCheck 37 c.val false w := by
  refine ⟨packetData0092.getD c.val 0,?_⟩
  have h := packetCheck_sound 37 false 0 packetData0092 packetPass0092 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_038 (c : Fin 4) : ∃w,BaseWitnessCheck 38 c.val false w := by
  refine ⟨packetData0093.getD c.val 0,?_⟩
  have h := packetCheck_sound 38 false 0 packetData0093 packetPass0093 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_039 (c : Fin 4) : ∃w,BaseWitnessCheck 39 c.val false w := by
  refine ⟨packetData0094.getD c.val 0,?_⟩
  have h := packetCheck_sound 39 false 0 packetData0094 packetPass0094 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_040 (c : Fin 4) : ∃w,BaseWitnessCheck 40 c.val false w := by
  refine ⟨packetData0095.getD c.val 0,?_⟩
  have h := packetCheck_sound 40 false 0 packetData0095 packetPass0095 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_041 (c : Fin 4) : ∃w,BaseWitnessCheck 41 c.val false w := by
  refine ⟨packetData0096.getD c.val 0,?_⟩
  have h := packetCheck_sound 41 false 0 packetData0096 packetPass0096 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_042 (c : Fin 4) : ∃w,BaseWitnessCheck 42 c.val false w := by
  refine ⟨packetData0097.getD c.val 0,?_⟩
  have h := packetCheck_sound 42 false 0 packetData0097 packetPass0097 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_043 (c : Fin 4) : ∃w,BaseWitnessCheck 43 c.val false w := by
  refine ⟨packetData0098.getD c.val 0,?_⟩
  have h := packetCheck_sound 43 false 0 packetData0098 packetPass0098 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_044 (c : Fin 4) : ∃w,BaseWitnessCheck 44 c.val false w := by
  refine ⟨packetData0099.getD c.val 0,?_⟩
  have h := packetCheck_sound 44 false 0 packetData0099 packetPass0099 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_045 (c : Fin 4) : ∃w,BaseWitnessCheck 45 c.val false w := by
  refine ⟨packetData0100.getD c.val 0,?_⟩
  have h := packetCheck_sound 45 false 0 packetData0100 packetPass0100 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_046 (c : Fin 4) : ∃w,BaseWitnessCheck 46 c.val false w := by
  refine ⟨packetData0101.getD c.val 0,?_⟩
  have h := packetCheck_sound 46 false 0 packetData0101 packetPass0101 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_047 (c : Fin 4) : ∃w,BaseWitnessCheck 47 c.val false w := by
  refine ⟨packetData0102.getD c.val 0,?_⟩
  have h := packetCheck_sound 47 false 0 packetData0102 packetPass0102 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_048 (c : Fin 4) : ∃w,BaseWitnessCheck 48 c.val false w := by
  refine ⟨packetData0103.getD c.val 0,?_⟩
  have h := packetCheck_sound 48 false 0 packetData0103 packetPass0103 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_049 (c : Fin 4) : ∃w,BaseWitnessCheck 49 c.val false w := by
  refine ⟨packetData0104.getD c.val 0,?_⟩
  have h := packetCheck_sound 49 false 0 packetData0104 packetPass0104 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_050 (c : Fin 4) : ∃w,BaseWitnessCheck 50 c.val false w := by
  refine ⟨packetData0105.getD c.val 0,?_⟩
  have h := packetCheck_sound 50 false 0 packetData0105 packetPass0105 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_051 (c : Fin 4) : ∃w,BaseWitnessCheck 51 c.val false w := by
  refine ⟨packetData0106.getD c.val 0,?_⟩
  have h := packetCheck_sound 51 false 0 packetData0106 packetPass0106 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_052 (c : Fin 4) : ∃w,BaseWitnessCheck 52 c.val false w := by
  refine ⟨packetData0107.getD c.val 0,?_⟩
  have h := packetCheck_sound 52 false 0 packetData0107 packetPass0107 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_053 (c : Fin 4) : ∃w,BaseWitnessCheck 53 c.val false w := by
  refine ⟨packetData0108.getD c.val 0,?_⟩
  have h := packetCheck_sound 53 false 0 packetData0108 packetPass0108 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_054 (c : Fin 4) : ∃w,BaseWitnessCheck 54 c.val false w := by
  refine ⟨packetData0109.getD c.val 0,?_⟩
  have h := packetCheck_sound 54 false 0 packetData0109 packetPass0109 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_055 (c : Fin 4) : ∃w,BaseWitnessCheck 55 c.val false w := by
  refine ⟨packetData0110.getD c.val 0,?_⟩
  have h := packetCheck_sound 55 false 0 packetData0110 packetPass0110 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_056 (c : Fin 4) : ∃w,BaseWitnessCheck 56 c.val false w := by
  refine ⟨packetData0111.getD c.val 0,?_⟩
  have h := packetCheck_sound 56 false 0 packetData0111 packetPass0111 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_057 (c : Fin 4) : ∃w,BaseWitnessCheck 57 c.val false w := by
  refine ⟨packetData0112.getD c.val 0,?_⟩
  have h := packetCheck_sound 57 false 0 packetData0112 packetPass0112 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_058 (c : Fin 4) : ∃w,BaseWitnessCheck 58 c.val false w := by
  refine ⟨packetData0113.getD c.val 0,?_⟩
  have h := packetCheck_sound 58 false 0 packetData0113 packetPass0113 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_059 (c : Fin 4) : ∃w,BaseWitnessCheck 59 c.val false w := by
  refine ⟨packetData0114.getD c.val 0,?_⟩
  have h := packetCheck_sound 59 false 0 packetData0114 packetPass0114 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_060 (c : Fin 4) : ∃w,BaseWitnessCheck 60 c.val false w := by
  refine ⟨packetData0115.getD c.val 0,?_⟩
  have h := packetCheck_sound 60 false 0 packetData0115 packetPass0115 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_061 (c : Fin 4) : ∃w,BaseWitnessCheck 61 c.val false w := by
  refine ⟨packetData0116.getD c.val 0,?_⟩
  have h := packetCheck_sound 61 false 0 packetData0116 packetPass0116 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_062 (c : Fin 4) : ∃w,BaseWitnessCheck 62 c.val false w := by
  refine ⟨packetData0117.getD c.val 0,?_⟩
  have h := packetCheck_sound 62 false 0 packetData0117 packetPass0117 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_063 (c : Fin 4) : ∃w,BaseWitnessCheck 63 c.val false w := by
  refine ⟨packetData0118.getD c.val 0,?_⟩
  have h := packetCheck_sound 63 false 0 packetData0118 packetPass0118 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_064 (c : Fin 4) : ∃w,BaseWitnessCheck 64 c.val false w := by
  refine ⟨packetData0119.getD c.val 0,?_⟩
  have h := packetCheck_sound 64 false 0 packetData0119 packetPass0119 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_065 (c : Fin 4) : ∃w,BaseWitnessCheck 65 c.val false w := by
  refine ⟨packetData0120.getD c.val 0,?_⟩
  have h := packetCheck_sound 65 false 0 packetData0120 packetPass0120 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_066 (c : Fin 4) : ∃w,BaseWitnessCheck 66 c.val false w := by
  refine ⟨packetData0121.getD c.val 0,?_⟩
  have h := packetCheck_sound 66 false 0 packetData0121 packetPass0121 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_067 (c : Fin 4) : ∃w,BaseWitnessCheck 67 c.val false w := by
  refine ⟨packetData0122.getD c.val 0,?_⟩
  have h := packetCheck_sound 67 false 0 packetData0122 packetPass0122 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_068 (c : Fin 4) : ∃w,BaseWitnessCheck 68 c.val false w := by
  refine ⟨packetData0123.getD c.val 0,?_⟩
  have h := packetCheck_sound 68 false 0 packetData0123 packetPass0123 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_069 (c : Fin 4) : ∃w,BaseWitnessCheck 69 c.val false w := by
  refine ⟨packetData0124.getD c.val 0,?_⟩
  have h := packetCheck_sound 69 false 0 packetData0124 packetPass0124 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_070 (c : Fin 4) : ∃w,BaseWitnessCheck 70 c.val false w := by
  refine ⟨packetData0125.getD c.val 0,?_⟩
  have h := packetCheck_sound 70 false 0 packetData0125 packetPass0125 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_071 (c : Fin 4) : ∃w,BaseWitnessCheck 71 c.val false w := by
  refine ⟨packetData0126.getD c.val 0,?_⟩
  have h := packetCheck_sound 71 false 0 packetData0126 packetPass0126 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_072 (c : Fin 4) : ∃w,BaseWitnessCheck 72 c.val false w := by
  refine ⟨packetData0127.getD c.val 0,?_⟩
  have h := packetCheck_sound 72 false 0 packetData0127 packetPass0127 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_073 (c : Fin 4) : ∃w,BaseWitnessCheck 73 c.val false w := by
  refine ⟨packetData0128.getD c.val 0,?_⟩
  have h := packetCheck_sound 73 false 0 packetData0128 packetPass0128 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_074 (c : Fin 4) : ∃w,BaseWitnessCheck 74 c.val false w := by
  refine ⟨packetData0129.getD c.val 0,?_⟩
  have h := packetCheck_sound 74 false 0 packetData0129 packetPass0129 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_075 (c : Fin 4) : ∃w,BaseWitnessCheck 75 c.val false w := by
  refine ⟨packetData0130.getD c.val 0,?_⟩
  have h := packetCheck_sound 75 false 0 packetData0130 packetPass0130 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_076 (c : Fin 4) : ∃w,BaseWitnessCheck 76 c.val false w := by
  refine ⟨packetData0131.getD c.val 0,?_⟩
  have h := packetCheck_sound 76 false 0 packetData0131 packetPass0131 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_077 (c : Fin 4) : ∃w,BaseWitnessCheck 77 c.val false w := by
  refine ⟨packetData0132.getD c.val 0,?_⟩
  have h := packetCheck_sound 77 false 0 packetData0132 packetPass0132 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_078 (c : Fin 4) : ∃w,BaseWitnessCheck 78 c.val false w := by
  refine ⟨packetData0133.getD c.val 0,?_⟩
  have h := packetCheck_sound 78 false 0 packetData0133 packetPass0133 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_079 (c : Fin 4) : ∃w,BaseWitnessCheck 79 c.val false w := by
  refine ⟨packetData0134.getD c.val 0,?_⟩
  have h := packetCheck_sound 79 false 0 packetData0134 packetPass0134 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_080 (c : Fin 4) : ∃w,BaseWitnessCheck 80 c.val false w := by
  refine ⟨packetData0135.getD c.val 0,?_⟩
  have h := packetCheck_sound 80 false 0 packetData0135 packetPass0135 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_081 (c : Fin 4) : ∃w,BaseWitnessCheck 81 c.val false w := by
  refine ⟨packetData0136.getD c.val 0,?_⟩
  have h := packetCheck_sound 81 false 0 packetData0136 packetPass0136 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_082 (c : Fin 4) : ∃w,BaseWitnessCheck 82 c.val false w := by
  refine ⟨packetData0137.getD c.val 0,?_⟩
  have h := packetCheck_sound 82 false 0 packetData0137 packetPass0137 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_083 (c : Fin 4) : ∃w,BaseWitnessCheck 83 c.val false w := by
  refine ⟨packetData0138.getD c.val 0,?_⟩
  have h := packetCheck_sound 83 false 0 packetData0138 packetPass0138 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_084 (c : Fin 4) : ∃w,BaseWitnessCheck 84 c.val false w := by
  refine ⟨packetData0139.getD c.val 0,?_⟩
  have h := packetCheck_sound 84 false 0 packetData0139 packetPass0139 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_085 (c : Fin 4) : ∃w,BaseWitnessCheck 85 c.val false w := by
  refine ⟨packetData0140.getD c.val 0,?_⟩
  have h := packetCheck_sound 85 false 0 packetData0140 packetPass0140 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_086 (c : Fin 4) : ∃w,BaseWitnessCheck 86 c.val false w := by
  refine ⟨packetData0141.getD c.val 0,?_⟩
  have h := packetCheck_sound 86 false 0 packetData0141 packetPass0141 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_087 (c : Fin 4) : ∃w,BaseWitnessCheck 87 c.val false w := by
  refine ⟨packetData0142.getD c.val 0,?_⟩
  have h := packetCheck_sound 87 false 0 packetData0142 packetPass0142 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_088 (c : Fin 4) : ∃w,BaseWitnessCheck 88 c.val false w := by
  refine ⟨packetData0143.getD c.val 0,?_⟩
  have h := packetCheck_sound 88 false 0 packetData0143 packetPass0143 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_089 (c : Fin 4) : ∃w,BaseWitnessCheck 89 c.val false w := by
  refine ⟨packetData0144.getD c.val 0,?_⟩
  have h := packetCheck_sound 89 false 0 packetData0144 packetPass0144 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_090 (c : Fin 4) : ∃w,BaseWitnessCheck 90 c.val false w := by
  refine ⟨packetData0145.getD c.val 0,?_⟩
  have h := packetCheck_sound 90 false 0 packetData0145 packetPass0145 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_091 (c : Fin 4) : ∃w,BaseWitnessCheck 91 c.val false w := by
  refine ⟨packetData0146.getD c.val 0,?_⟩
  have h := packetCheck_sound 91 false 0 packetData0146 packetPass0146 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_092 (c : Fin 4) : ∃w,BaseWitnessCheck 92 c.val false w := by
  refine ⟨packetData0147.getD c.val 0,?_⟩
  have h := packetCheck_sound 92 false 0 packetData0147 packetPass0147 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_093 (c : Fin 4) : ∃w,BaseWitnessCheck 93 c.val false w := by
  refine ⟨packetData0148.getD c.val 0,?_⟩
  have h := packetCheck_sound 93 false 0 packetData0148 packetPass0148 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_094 (c : Fin 4) : ∃w,BaseWitnessCheck 94 c.val false w := by
  refine ⟨packetData0149.getD c.val 0,?_⟩
  have h := packetCheck_sound 94 false 0 packetData0149 packetPass0149 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_095 (c : Fin 4) : ∃w,BaseWitnessCheck 95 c.val false w := by
  refine ⟨packetData0150.getD c.val 0,?_⟩
  have h := packetCheck_sound 95 false 0 packetData0150 packetPass0150 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_096 (c : Fin 4) : ∃w,BaseWitnessCheck 96 c.val false w := by
  refine ⟨packetData0151.getD c.val 0,?_⟩
  have h := packetCheck_sound 96 false 0 packetData0151 packetPass0151 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_097 (c : Fin 4) : ∃w,BaseWitnessCheck 97 c.val false w := by
  refine ⟨packetData0152.getD c.val 0,?_⟩
  have h := packetCheck_sound 97 false 0 packetData0152 packetPass0152 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_098 (c : Fin 4) : ∃w,BaseWitnessCheck 98 c.val false w := by
  refine ⟨packetData0153.getD c.val 0,?_⟩
  have h := packetCheck_sound 98 false 0 packetData0153 packetPass0153 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_099 (c : Fin 4) : ∃w,BaseWitnessCheck 99 c.val false w := by
  refine ⟨packetData0154.getD c.val 0,?_⟩
  have h := packetCheck_sound 99 false 0 packetData0154 packetPass0154 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_100 (c : Fin 4) : ∃w,BaseWitnessCheck 100 c.val false w := by
  refine ⟨packetData0155.getD c.val 0,?_⟩
  have h := packetCheck_sound 100 false 0 packetData0155 packetPass0155 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_101 (c : Fin 4) : ∃w,BaseWitnessCheck 101 c.val false w := by
  refine ⟨packetData0156.getD c.val 0,?_⟩
  have h := packetCheck_sound 101 false 0 packetData0156 packetPass0156 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_102 (c : Fin 4) : ∃w,BaseWitnessCheck 102 c.val false w := by
  refine ⟨packetData0157.getD c.val 0,?_⟩
  have h := packetCheck_sound 102 false 0 packetData0157 packetPass0157 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_103 (c : Fin 4) : ∃w,BaseWitnessCheck 103 c.val false w := by
  refine ⟨packetData0158.getD c.val 0,?_⟩
  have h := packetCheck_sound 103 false 0 packetData0158 packetPass0158 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_104 (c : Fin 4) : ∃w,BaseWitnessCheck 104 c.val false w := by
  refine ⟨packetData0159.getD c.val 0,?_⟩
  have h := packetCheck_sound 104 false 0 packetData0159 packetPass0159 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_105 (c : Fin 4) : ∃w,BaseWitnessCheck 105 c.val false w := by
  refine ⟨packetData0160.getD c.val 0,?_⟩
  have h := packetCheck_sound 105 false 0 packetData0160 packetPass0160 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_106 (c : Fin 4) : ∃w,BaseWitnessCheck 106 c.val false w := by
  refine ⟨packetData0161.getD c.val 0,?_⟩
  have h := packetCheck_sound 106 false 0 packetData0161 packetPass0161 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_107 (c : Fin 4) : ∃w,BaseWitnessCheck 107 c.val false w := by
  refine ⟨packetData0162.getD c.val 0,?_⟩
  have h := packetCheck_sound 107 false 0 packetData0162 packetPass0162 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_108 (c : Fin 4) : ∃w,BaseWitnessCheck 108 c.val false w := by
  refine ⟨packetData0163.getD c.val 0,?_⟩
  have h := packetCheck_sound 108 false 0 packetData0163 packetPass0163 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_109 (c : Fin 4) : ∃w,BaseWitnessCheck 109 c.val false w := by
  refine ⟨packetData0164.getD c.val 0,?_⟩
  have h := packetCheck_sound 109 false 0 packetData0164 packetPass0164 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_110 (c : Fin 4) : ∃w,BaseWitnessCheck 110 c.val false w := by
  refine ⟨packetData0165.getD c.val 0,?_⟩
  have h := packetCheck_sound 110 false 0 packetData0165 packetPass0165 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_111 (c : Fin 4) : ∃w,BaseWitnessCheck 111 c.val false w := by
  refine ⟨packetData0166.getD c.val 0,?_⟩
  have h := packetCheck_sound 111 false 0 packetData0166 packetPass0166 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_112 (c : Fin 4) : ∃w,BaseWitnessCheck 112 c.val false w := by
  refine ⟨packetData0167.getD c.val 0,?_⟩
  have h := packetCheck_sound 112 false 0 packetData0167 packetPass0167 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_113 (c : Fin 4) : ∃w,BaseWitnessCheck 113 c.val false w := by
  refine ⟨packetData0168.getD c.val 0,?_⟩
  have h := packetCheck_sound 113 false 0 packetData0168 packetPass0168 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_114 (c : Fin 4) : ∃w,BaseWitnessCheck 114 c.val false w := by
  refine ⟨packetData0169.getD c.val 0,?_⟩
  have h := packetCheck_sound 114 false 0 packetData0169 packetPass0169 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_115 (c : Fin 4) : ∃w,BaseWitnessCheck 115 c.val false w := by
  refine ⟨packetData0170.getD c.val 0,?_⟩
  have h := packetCheck_sound 115 false 0 packetData0170 packetPass0170 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_116 (c : Fin 4) : ∃w,BaseWitnessCheck 116 c.val false w := by
  refine ⟨packetData0171.getD c.val 0,?_⟩
  have h := packetCheck_sound 116 false 0 packetData0171 packetPass0171 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_117 (c : Fin 4) : ∃w,BaseWitnessCheck 117 c.val false w := by
  refine ⟨packetData0172.getD c.val 0,?_⟩
  have h := packetCheck_sound 117 false 0 packetData0172 packetPass0172 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_118 (c : Fin 4) : ∃w,BaseWitnessCheck 118 c.val false w := by
  refine ⟨packetData0173.getD c.val 0,?_⟩
  have h := packetCheck_sound 118 false 0 packetData0173 packetPass0173 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_119 (c : Fin 4) : ∃w,BaseWitnessCheck 119 c.val false w := by
  refine ⟨packetData0174.getD c.val 0,?_⟩
  have h := packetCheck_sound 119 false 0 packetData0174 packetPass0174 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_120 (c : Fin 4) : ∃w,BaseWitnessCheck 120 c.val false w := by
  refine ⟨packetData0175.getD c.val 0,?_⟩
  have h := packetCheck_sound 120 false 0 packetData0175 packetPass0175 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_121 (c : Fin 4) : ∃w,BaseWitnessCheck 121 c.val false w := by
  refine ⟨packetData0176.getD c.val 0,?_⟩
  have h := packetCheck_sound 121 false 0 packetData0176 packetPass0176 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_122 (c : Fin 4) : ∃w,BaseWitnessCheck 122 c.val false w := by
  refine ⟨packetData0177.getD c.val 0,?_⟩
  have h := packetCheck_sound 122 false 0 packetData0177 packetPass0177 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_123 (c : Fin 4) : ∃w,BaseWitnessCheck 123 c.val false w := by
  refine ⟨packetData0178.getD c.val 0,?_⟩
  have h := packetCheck_sound 123 false 0 packetData0178 packetPass0178 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_124 (c : Fin 4) : ∃w,BaseWitnessCheck 124 c.val false w := by
  refine ⟨packetData0179.getD c.val 0,?_⟩
  have h := packetCheck_sound 124 false 0 packetData0179 packetPass0179 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_125 (c : Fin 4) : ∃w,BaseWitnessCheck 125 c.val false w := by
  refine ⟨packetData0180.getD c.val 0,?_⟩
  have h := packetCheck_sound 125 false 0 packetData0180 packetPass0180 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_126 (c : Fin 4) : ∃w,BaseWitnessCheck 126 c.val false w := by
  refine ⟨packetData0181.getD c.val 0,?_⟩
  have h := packetCheck_sound 126 false 0 packetData0181 packetPass0181 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_127 (c : Fin 4) : ∃w,BaseWitnessCheck 127 c.val false w := by
  refine ⟨packetData0182.getD c.val 0,?_⟩
  have h := packetCheck_sound 127 false 0 packetData0182 packetPass0182 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_128 (c : Fin 4) : ∃w,BaseWitnessCheck 128 c.val false w := by
  refine ⟨packetData0000.getD c.val 0,?_⟩
  have h := packetCheck_sound 128 false 0 packetData0000 packetPass0000 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_129 (c : Fin 4) : ∃w,BaseWitnessCheck 129 c.val false w := by
  refine ⟨packetData0001.getD c.val 0,?_⟩
  have h := packetCheck_sound 129 false 0 packetData0001 packetPass0001 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_130 (c : Fin 4) : ∃w,BaseWitnessCheck 130 c.val false w := by
  refine ⟨packetData0002.getD c.val 0,?_⟩
  have h := packetCheck_sound 130 false 0 packetData0002 packetPass0002 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_131 (c : Fin 4) : ∃w,BaseWitnessCheck 131 c.val false w := by
  refine ⟨packetData0003.getD c.val 0,?_⟩
  have h := packetCheck_sound 131 false 0 packetData0003 packetPass0003 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_132 (c : Fin 4) : ∃w,BaseWitnessCheck 132 c.val false w := by
  refine ⟨packetData0004.getD c.val 0,?_⟩
  have h := packetCheck_sound 132 false 0 packetData0004 packetPass0004 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_133 (c : Fin 4) : ∃w,BaseWitnessCheck 133 c.val false w := by
  refine ⟨packetData0005.getD c.val 0,?_⟩
  have h := packetCheck_sound 133 false 0 packetData0005 packetPass0005 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_134 (c : Fin 4) : ∃w,BaseWitnessCheck 134 c.val false w := by
  refine ⟨packetData0006.getD c.val 0,?_⟩
  have h := packetCheck_sound 134 false 0 packetData0006 packetPass0006 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_135 (c : Fin 4) : ∃w,BaseWitnessCheck 135 c.val false w := by
  refine ⟨packetData0007.getD c.val 0,?_⟩
  have h := packetCheck_sound 135 false 0 packetData0007 packetPass0007 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_136 (c : Fin 32) : ∃w,BaseWitnessCheck 136 c.val false w := by
  refine ⟨packetData0183.getD c.val 0,?_⟩
  have h := packetCheck_sound 136 false 0 packetData0183 packetPass0183 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_137 (c : Fin 32) : ∃w,BaseWitnessCheck 137 c.val false w := by
  refine ⟨packetData0184.getD c.val 0,?_⟩
  have h := packetCheck_sound 137 false 0 packetData0184 packetPass0184 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_138 (c : Fin 32) : ∃w,BaseWitnessCheck 138 c.val false w := by
  refine ⟨packetData0185.getD c.val 0,?_⟩
  have h := packetCheck_sound 138 false 0 packetData0185 packetPass0185 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_139 (c : Fin 32) : ∃w,BaseWitnessCheck 139 c.val false w := by
  refine ⟨packetData0186.getD c.val 0,?_⟩
  have h := packetCheck_sound 139 false 0 packetData0186 packetPass0186 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_140 (c : Fin 32) : ∃w,BaseWitnessCheck 140 c.val false w := by
  refine ⟨packetData0187.getD c.val 0,?_⟩
  have h := packetCheck_sound 140 false 0 packetData0187 packetPass0187 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_141 (c : Fin 32) : ∃w,BaseWitnessCheck 141 c.val false w := by
  refine ⟨packetData0188.getD c.val 0,?_⟩
  have h := packetCheck_sound 141 false 0 packetData0188 packetPass0188 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_142 (c : Fin 32) : ∃w,BaseWitnessCheck 142 c.val false w := by
  refine ⟨packetData0189.getD c.val 0,?_⟩
  have h := packetCheck_sound 142 false 0 packetData0189 packetPass0189 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_143 (c : Fin 32) : ∃w,BaseWitnessCheck 143 c.val false w := by
  refine ⟨packetData0190.getD c.val 0,?_⟩
  have h := packetCheck_sound 143 false 0 packetData0190 packetPass0190 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_144 (c : Fin 32) : ∃w,BaseWitnessCheck 144 c.val false w := by
  refine ⟨packetData0191.getD c.val 0,?_⟩
  have h := packetCheck_sound 144 false 0 packetData0191 packetPass0191 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_145 (c : Fin 32) : ∃w,BaseWitnessCheck 145 c.val false w := by
  refine ⟨packetData0192.getD c.val 0,?_⟩
  have h := packetCheck_sound 145 false 0 packetData0192 packetPass0192 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_146 (c : Fin 32) : ∃w,BaseWitnessCheck 146 c.val false w := by
  refine ⟨packetData0193.getD c.val 0,?_⟩
  have h := packetCheck_sound 146 false 0 packetData0193 packetPass0193 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_147 (c : Fin 32) : ∃w,BaseWitnessCheck 147 c.val false w := by
  refine ⟨packetData0194.getD c.val 0,?_⟩
  have h := packetCheck_sound 147 false 0 packetData0194 packetPass0194 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_148 (c : Fin 32) : ∃w,BaseWitnessCheck 148 c.val false w := by
  refine ⟨packetData0195.getD c.val 0,?_⟩
  have h := packetCheck_sound 148 false 0 packetData0195 packetPass0195 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_149 (c : Fin 32) : ∃w,BaseWitnessCheck 149 c.val false w := by
  refine ⟨packetData0196.getD c.val 0,?_⟩
  have h := packetCheck_sound 149 false 0 packetData0196 packetPass0196 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_150 (c : Fin 32) : ∃w,BaseWitnessCheck 150 c.val false w := by
  refine ⟨packetData0197.getD c.val 0,?_⟩
  have h := packetCheck_sound 150 false 0 packetData0197 packetPass0197 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_151 (c : Fin 32) : ∃w,BaseWitnessCheck 151 c.val false w := by
  refine ⟨packetData0198.getD c.val 0,?_⟩
  have h := packetCheck_sound 151 false 0 packetData0198 packetPass0198 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_152 (c : Fin 32) : ∃w,BaseWitnessCheck 152 c.val false w := by
  refine ⟨packetData0199.getD c.val 0,?_⟩
  have h := packetCheck_sound 152 false 0 packetData0199 packetPass0199 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_153 (c : Fin 32) : ∃w,BaseWitnessCheck 153 c.val false w := by
  refine ⟨packetData0200.getD c.val 0,?_⟩
  have h := packetCheck_sound 153 false 0 packetData0200 packetPass0200 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_154 (c : Fin 32) : ∃w,BaseWitnessCheck 154 c.val false w := by
  refine ⟨packetData0201.getD c.val 0,?_⟩
  have h := packetCheck_sound 154 false 0 packetData0201 packetPass0201 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_155 (c : Fin 32) : ∃w,BaseWitnessCheck 155 c.val false w := by
  refine ⟨packetData0202.getD c.val 0,?_⟩
  have h := packetCheck_sound 155 false 0 packetData0202 packetPass0202 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_156 (c : Fin 32) : ∃w,BaseWitnessCheck 156 c.val false w := by
  refine ⟨packetData0203.getD c.val 0,?_⟩
  have h := packetCheck_sound 156 false 0 packetData0203 packetPass0203 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_157 (c : Fin 32) : ∃w,BaseWitnessCheck 157 c.val false w := by
  refine ⟨packetData0204.getD c.val 0,?_⟩
  have h := packetCheck_sound 157 false 0 packetData0204 packetPass0204 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_158 (c : Fin 32) : ∃w,BaseWitnessCheck 158 c.val false w := by
  refine ⟨packetData0205.getD c.val 0,?_⟩
  have h := packetCheck_sound 158 false 0 packetData0205 packetPass0205 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_159 (c : Fin 32) : ∃w,BaseWitnessCheck 159 c.val false w := by
  refine ⟨packetData0206.getD c.val 0,?_⟩
  have h := packetCheck_sound 159 false 0 packetData0206 packetPass0206 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_160 (c : Fin 32) : ∃w,BaseWitnessCheck 160 c.val false w := by
  refine ⟨packetData0207.getD c.val 0,?_⟩
  have h := packetCheck_sound 160 false 0 packetData0207 packetPass0207 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_161 (c : Fin 32) : ∃w,BaseWitnessCheck 161 c.val false w := by
  refine ⟨packetData0208.getD c.val 0,?_⟩
  have h := packetCheck_sound 161 false 0 packetData0208 packetPass0208 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_162 (c : Fin 32) : ∃w,BaseWitnessCheck 162 c.val false w := by
  refine ⟨packetData0209.getD c.val 0,?_⟩
  have h := packetCheck_sound 162 false 0 packetData0209 packetPass0209 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_163 (c : Fin 32) : ∃w,BaseWitnessCheck 163 c.val false w := by
  refine ⟨packetData0210.getD c.val 0,?_⟩
  have h := packetCheck_sound 163 false 0 packetData0210 packetPass0210 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_164 (c : Fin 32) : ∃w,BaseWitnessCheck 164 c.val false w := by
  refine ⟨packetData0211.getD c.val 0,?_⟩
  have h := packetCheck_sound 164 false 0 packetData0211 packetPass0211 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_165 (c : Fin 32) : ∃w,BaseWitnessCheck 165 c.val false w := by
  refine ⟨packetData0212.getD c.val 0,?_⟩
  have h := packetCheck_sound 165 false 0 packetData0212 packetPass0212 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_166 (c : Fin 32) : ∃w,BaseWitnessCheck 166 c.val false w := by
  refine ⟨packetData0213.getD c.val 0,?_⟩
  have h := packetCheck_sound 166 false 0 packetData0213 packetPass0213 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_167 (c : Fin 32) : ∃w,BaseWitnessCheck 167 c.val false w := by
  refine ⟨packetData0214.getD c.val 0,?_⟩
  have h := packetCheck_sound 167 false 0 packetData0214 packetPass0214 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_168 (c : Fin 32) : ∃w,BaseWitnessCheck 168 c.val false w := by
  refine ⟨packetData0215.getD c.val 0,?_⟩
  have h := packetCheck_sound 168 false 0 packetData0215 packetPass0215 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_169 (c : Fin 32) : ∃w,BaseWitnessCheck 169 c.val false w := by
  refine ⟨packetData0216.getD c.val 0,?_⟩
  have h := packetCheck_sound 169 false 0 packetData0216 packetPass0216 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_170 (c : Fin 32) : ∃w,BaseWitnessCheck 170 c.val false w := by
  refine ⟨packetData0217.getD c.val 0,?_⟩
  have h := packetCheck_sound 170 false 0 packetData0217 packetPass0217 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_171 (c : Fin 32) : ∃w,BaseWitnessCheck 171 c.val false w := by
  refine ⟨packetData0218.getD c.val 0,?_⟩
  have h := packetCheck_sound 171 false 0 packetData0218 packetPass0218 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_172 (c : Fin 32) : ∃w,BaseWitnessCheck 172 c.val false w := by
  refine ⟨packetData0219.getD c.val 0,?_⟩
  have h := packetCheck_sound 172 false 0 packetData0219 packetPass0219 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_173 (c : Fin 32) : ∃w,BaseWitnessCheck 173 c.val false w := by
  refine ⟨packetData0220.getD c.val 0,?_⟩
  have h := packetCheck_sound 173 false 0 packetData0220 packetPass0220 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_174 (c : Fin 32) : ∃w,BaseWitnessCheck 174 c.val false w := by
  refine ⟨packetData0221.getD c.val 0,?_⟩
  have h := packetCheck_sound 174 false 0 packetData0221 packetPass0221 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_175 (c : Fin 32) : ∃w,BaseWitnessCheck 175 c.val false w := by
  refine ⟨packetData0222.getD c.val 0,?_⟩
  have h := packetCheck_sound 175 false 0 packetData0222 packetPass0222 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_176 (c : Fin 32) : ∃w,BaseWitnessCheck 176 c.val false w := by
  refine ⟨packetData0223.getD c.val 0,?_⟩
  have h := packetCheck_sound 176 false 0 packetData0223 packetPass0223 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_177 (c : Fin 32) : ∃w,BaseWitnessCheck 177 c.val false w := by
  refine ⟨packetData0224.getD c.val 0,?_⟩
  have h := packetCheck_sound 177 false 0 packetData0224 packetPass0224 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_178 (c : Fin 32) : ∃w,BaseWitnessCheck 178 c.val false w := by
  refine ⟨packetData0225.getD c.val 0,?_⟩
  have h := packetCheck_sound 178 false 0 packetData0225 packetPass0225 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_179 (c : Fin 32) : ∃w,BaseWitnessCheck 179 c.val false w := by
  refine ⟨packetData0226.getD c.val 0,?_⟩
  have h := packetCheck_sound 179 false 0 packetData0226 packetPass0226 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_180 (c : Fin 32) : ∃w,BaseWitnessCheck 180 c.val false w := by
  refine ⟨packetData0227.getD c.val 0,?_⟩
  have h := packetCheck_sound 180 false 0 packetData0227 packetPass0227 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_181 (c : Fin 32) : ∃w,BaseWitnessCheck 181 c.val false w := by
  refine ⟨packetData0228.getD c.val 0,?_⟩
  have h := packetCheck_sound 181 false 0 packetData0228 packetPass0228 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_182 (c : Fin 32) : ∃w,BaseWitnessCheck 182 c.val false w := by
  refine ⟨packetData0229.getD c.val 0,?_⟩
  have h := packetCheck_sound 182 false 0 packetData0229 packetPass0229 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_183 (c : Fin 32) : ∃w,BaseWitnessCheck 183 c.val false w := by
  refine ⟨packetData0230.getD c.val 0,?_⟩
  have h := packetCheck_sound 183 false 0 packetData0230 packetPass0230 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_184 (c : Fin 32) : ∃w,BaseWitnessCheck 184 c.val false w := by
  refine ⟨packetData0231.getD c.val 0,?_⟩
  have h := packetCheck_sound 184 false 0 packetData0231 packetPass0231 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_185 (c : Fin 32) : ∃w,BaseWitnessCheck 185 c.val false w := by
  refine ⟨packetData0232.getD c.val 0,?_⟩
  have h := packetCheck_sound 185 false 0 packetData0232 packetPass0232 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_186 (c : Fin 32) : ∃w,BaseWitnessCheck 186 c.val false w := by
  refine ⟨packetData0233.getD c.val 0,?_⟩
  have h := packetCheck_sound 186 false 0 packetData0233 packetPass0233 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_187 (c : Fin 32) : ∃w,BaseWitnessCheck 187 c.val false w := by
  refine ⟨packetData0234.getD c.val 0,?_⟩
  have h := packetCheck_sound 187 false 0 packetData0234 packetPass0234 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_188 (c : Fin 32) : ∃w,BaseWitnessCheck 188 c.val false w := by
  refine ⟨packetData0235.getD c.val 0,?_⟩
  have h := packetCheck_sound 188 false 0 packetData0235 packetPass0235 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_189 (c : Fin 32) : ∃w,BaseWitnessCheck 189 c.val false w := by
  refine ⟨packetData0236.getD c.val 0,?_⟩
  have h := packetCheck_sound 189 false 0 packetData0236 packetPass0236 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_190 (c : Fin 32) : ∃w,BaseWitnessCheck 190 c.val false w := by
  refine ⟨packetData0237.getD c.val 0,?_⟩
  have h := packetCheck_sound 190 false 0 packetData0237 packetPass0237 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_191 (c : Fin 32) : ∃w,BaseWitnessCheck 191 c.val false w := by
  refine ⟨packetData0238.getD c.val 0,?_⟩
  have h := packetCheck_sound 191 false 0 packetData0238 packetPass0238 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_192 (c : Fin 32) : ∃w,BaseWitnessCheck 192 c.val false w := by
  refine ⟨packetData0239.getD c.val 0,?_⟩
  have h := packetCheck_sound 192 false 0 packetData0239 packetPass0239 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_193 (c : Fin 32) : ∃w,BaseWitnessCheck 193 c.val false w := by
  refine ⟨packetData0240.getD c.val 0,?_⟩
  have h := packetCheck_sound 193 false 0 packetData0240 packetPass0240 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_194 (c : Fin 32) : ∃w,BaseWitnessCheck 194 c.val false w := by
  refine ⟨packetData0241.getD c.val 0,?_⟩
  have h := packetCheck_sound 194 false 0 packetData0241 packetPass0241 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_195 (c : Fin 32) : ∃w,BaseWitnessCheck 195 c.val false w := by
  refine ⟨packetData0242.getD c.val 0,?_⟩
  have h := packetCheck_sound 195 false 0 packetData0242 packetPass0242 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_196 (c : Fin 32) : ∃w,BaseWitnessCheck 196 c.val false w := by
  refine ⟨packetData0243.getD c.val 0,?_⟩
  have h := packetCheck_sound 196 false 0 packetData0243 packetPass0243 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_197 (c : Fin 32) : ∃w,BaseWitnessCheck 197 c.val false w := by
  refine ⟨packetData0244.getD c.val 0,?_⟩
  have h := packetCheck_sound 197 false 0 packetData0244 packetPass0244 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_198 (c : Fin 32) : ∃w,BaseWitnessCheck 198 c.val false w := by
  refine ⟨packetData0245.getD c.val 0,?_⟩
  have h := packetCheck_sound 198 false 0 packetData0245 packetPass0245 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_199 (c : Fin 32) : ∃w,BaseWitnessCheck 199 c.val false w := by
  refine ⟨packetData0246.getD c.val 0,?_⟩
  have h := packetCheck_sound 199 false 0 packetData0246 packetPass0246 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_200 (c : Fin 32) : ∃w,BaseWitnessCheck 200 c.val false w := by
  refine ⟨packetData0247.getD c.val 0,?_⟩
  have h := packetCheck_sound 200 false 0 packetData0247 packetPass0247 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_201 (c : Fin 32) : ∃w,BaseWitnessCheck 201 c.val false w := by
  refine ⟨packetData0248.getD c.val 0,?_⟩
  have h := packetCheck_sound 201 false 0 packetData0248 packetPass0248 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_202 (c : Fin 32) : ∃w,BaseWitnessCheck 202 c.val false w := by
  refine ⟨packetData0249.getD c.val 0,?_⟩
  have h := packetCheck_sound 202 false 0 packetData0249 packetPass0249 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_203 (c : Fin 32) : ∃w,BaseWitnessCheck 203 c.val false w := by
  refine ⟨packetData0250.getD c.val 0,?_⟩
  have h := packetCheck_sound 203 false 0 packetData0250 packetPass0250 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_204 (c : Fin 32) : ∃w,BaseWitnessCheck 204 c.val false w := by
  refine ⟨packetData0008.getD c.val 0,?_⟩
  have h := packetCheck_sound 204 false 0 packetData0008 packetPass0008 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_205 (c : Fin 32) : ∃w,BaseWitnessCheck 205 c.val false w := by
  refine ⟨packetData0009.getD c.val 0,?_⟩
  have h := packetCheck_sound 205 false 0 packetData0009 packetPass0009 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_206 (c : Fin 32) : ∃w,BaseWitnessCheck 206 c.val false w := by
  refine ⟨packetData0010.getD c.val 0,?_⟩
  have h := packetCheck_sound 206 false 0 packetData0010 packetPass0010 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_207 (c : Fin 32) : ∃w,BaseWitnessCheck 207 c.val false w := by
  refine ⟨packetData0011.getD c.val 0,?_⟩
  have h := packetCheck_sound 207 false 0 packetData0011 packetPass0011 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_208 (c : Fin 32) : ∃w,BaseWitnessCheck 208 c.val false w := by
  refine ⟨packetData0251.getD c.val 0,?_⟩
  have h := packetCheck_sound 208 false 0 packetData0251 packetPass0251 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_209 (c : Fin 32) : ∃w,BaseWitnessCheck 209 c.val false w := by
  refine ⟨packetData0252.getD c.val 0,?_⟩
  have h := packetCheck_sound 209 false 0 packetData0252 packetPass0252 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_210 (c : Fin 32) : ∃w,BaseWitnessCheck 210 c.val false w := by
  refine ⟨packetData0253.getD c.val 0,?_⟩
  have h := packetCheck_sound 210 false 0 packetData0253 packetPass0253 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_211 (c : Fin 32) : ∃w,BaseWitnessCheck 211 c.val false w := by
  refine ⟨packetData0254.getD c.val 0,?_⟩
  have h := packetCheck_sound 211 false 0 packetData0254 packetPass0254 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_212 (c : Fin 32) : ∃w,BaseWitnessCheck 212 c.val false w := by
  refine ⟨packetData0255.getD c.val 0,?_⟩
  have h := packetCheck_sound 212 false 0 packetData0255 packetPass0255 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_213 (c : Fin 32) : ∃w,BaseWitnessCheck 213 c.val false w := by
  refine ⟨packetData0256.getD c.val 0,?_⟩
  have h := packetCheck_sound 213 false 0 packetData0256 packetPass0256 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_214 (c : Fin 32) : ∃w,BaseWitnessCheck 214 c.val false w := by
  refine ⟨packetData0257.getD c.val 0,?_⟩
  have h := packetCheck_sound 214 false 0 packetData0257 packetPass0257 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_215 (c : Fin 32) : ∃w,BaseWitnessCheck 215 c.val false w := by
  refine ⟨packetData0258.getD c.val 0,?_⟩
  have h := packetCheck_sound 215 false 0 packetData0258 packetPass0258 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_216 (c : Fin 32) : ∃w,BaseWitnessCheck 216 c.val false w := by
  refine ⟨packetData0259.getD c.val 0,?_⟩
  have h := packetCheck_sound 216 false 0 packetData0259 packetPass0259 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_217 (c : Fin 32) : ∃w,BaseWitnessCheck 217 c.val false w := by
  refine ⟨packetData0260.getD c.val 0,?_⟩
  have h := packetCheck_sound 217 false 0 packetData0260 packetPass0260 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_218 (c : Fin 32) : ∃w,BaseWitnessCheck 218 c.val false w := by
  refine ⟨packetData0261.getD c.val 0,?_⟩
  have h := packetCheck_sound 218 false 0 packetData0261 packetPass0261 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_219 (c : Fin 32) : ∃w,BaseWitnessCheck 219 c.val false w := by
  refine ⟨packetData0262.getD c.val 0,?_⟩
  have h := packetCheck_sound 219 false 0 packetData0262 packetPass0262 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_220 (c : Fin 32) : ∃w,BaseWitnessCheck 220 c.val false w := by
  refine ⟨packetData0263.getD c.val 0,?_⟩
  have h := packetCheck_sound 220 false 0 packetData0263 packetPass0263 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_221 (c : Fin 32) : ∃w,BaseWitnessCheck 221 c.val false w := by
  refine ⟨packetData0264.getD c.val 0,?_⟩
  have h := packetCheck_sound 221 false 0 packetData0264 packetPass0264 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_222 (c : Fin 32) : ∃w,BaseWitnessCheck 222 c.val false w := by
  refine ⟨packetData0265.getD c.val 0,?_⟩
  have h := packetCheck_sound 222 false 0 packetData0265 packetPass0265 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_223 (c : Fin 32) : ∃w,BaseWitnessCheck 223 c.val false w := by
  refine ⟨packetData0266.getD c.val 0,?_⟩
  have h := packetCheck_sound 223 false 0 packetData0266 packetPass0266 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_224 (c : Fin 32) : ∃w,BaseWitnessCheck 224 c.val false w := by
  refine ⟨packetData0267.getD c.val 0,?_⟩
  have h := packetCheck_sound 224 false 0 packetData0267 packetPass0267 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_225 (c : Fin 32) : ∃w,BaseWitnessCheck 225 c.val false w := by
  refine ⟨packetData0268.getD c.val 0,?_⟩
  have h := packetCheck_sound 225 false 0 packetData0268 packetPass0268 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_226 (c : Fin 32) : ∃w,BaseWitnessCheck 226 c.val false w := by
  refine ⟨packetData0269.getD c.val 0,?_⟩
  have h := packetCheck_sound 226 false 0 packetData0269 packetPass0269 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_227 (c : Fin 32) : ∃w,BaseWitnessCheck 227 c.val false w := by
  refine ⟨packetData0270.getD c.val 0,?_⟩
  have h := packetCheck_sound 227 false 0 packetData0270 packetPass0270 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_228 (c : Fin 32) : ∃w,BaseWitnessCheck 228 c.val false w := by
  refine ⟨packetData0271.getD c.val 0,?_⟩
  have h := packetCheck_sound 228 false 0 packetData0271 packetPass0271 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_229 (c : Fin 32) : ∃w,BaseWitnessCheck 229 c.val false w := by
  refine ⟨packetData0272.getD c.val 0,?_⟩
  have h := packetCheck_sound 229 false 0 packetData0272 packetPass0272 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_230 (c : Fin 32) : ∃w,BaseWitnessCheck 230 c.val false w := by
  refine ⟨packetData0273.getD c.val 0,?_⟩
  have h := packetCheck_sound 230 false 0 packetData0273 packetPass0273 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_231 (c : Fin 32) : ∃w,BaseWitnessCheck 231 c.val false w := by
  refine ⟨packetData0274.getD c.val 0,?_⟩
  have h := packetCheck_sound 231 false 0 packetData0274 packetPass0274 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_232 (c : Fin 32) : ∃w,BaseWitnessCheck 232 c.val false w := by
  refine ⟨packetData0275.getD c.val 0,?_⟩
  have h := packetCheck_sound 232 false 0 packetData0275 packetPass0275 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_233 (c : Fin 32) : ∃w,BaseWitnessCheck 233 c.val false w := by
  refine ⟨packetData0276.getD c.val 0,?_⟩
  have h := packetCheck_sound 233 false 0 packetData0276 packetPass0276 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_234 (c : Fin 32) : ∃w,BaseWitnessCheck 234 c.val false w := by
  refine ⟨packetData0277.getD c.val 0,?_⟩
  have h := packetCheck_sound 234 false 0 packetData0277 packetPass0277 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_235 (c : Fin 32) : ∃w,BaseWitnessCheck 235 c.val false w := by
  refine ⟨packetData0278.getD c.val 0,?_⟩
  have h := packetCheck_sound 235 false 0 packetData0278 packetPass0278 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_236 (c : Fin 32) : ∃w,BaseWitnessCheck 236 c.val false w := by
  refine ⟨packetData0012.getD c.val 0,?_⟩
  have h := packetCheck_sound 236 false 0 packetData0012 packetPass0012 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_237 (c : Fin 32) : ∃w,BaseWitnessCheck 237 c.val false w := by
  refine ⟨packetData0013.getD c.val 0,?_⟩
  have h := packetCheck_sound 237 false 0 packetData0013 packetPass0013 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_238 (c : Fin 32) : ∃w,BaseWitnessCheck 238 c.val false w := by
  refine ⟨packetData0014.getD c.val 0,?_⟩
  have h := packetCheck_sound 238 false 0 packetData0014 packetPass0014 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_239 (c : Fin 32) : ∃w,BaseWitnessCheck 239 c.val false w := by
  refine ⟨packetData0015.getD c.val 0,?_⟩
  have h := packetCheck_sound 239 false 0 packetData0015 packetPass0015 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_240 (c : Fin 32) : ∃w,BaseWitnessCheck 240 c.val false w := by
  refine ⟨packetData0279.getD c.val 0,?_⟩
  have h := packetCheck_sound 240 false 0 packetData0279 packetPass0279 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_241 (c : Fin 32) : ∃w,BaseWitnessCheck 241 c.val false w := by
  refine ⟨packetData0280.getD c.val 0,?_⟩
  have h := packetCheck_sound 241 false 0 packetData0280 packetPass0280 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_242 (c : Fin 32) : ∃w,BaseWitnessCheck 242 c.val false w := by
  refine ⟨packetData0281.getD c.val 0,?_⟩
  have h := packetCheck_sound 242 false 0 packetData0281 packetPass0281 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_243 (c : Fin 32) : ∃w,BaseWitnessCheck 243 c.val false w := by
  refine ⟨packetData0282.getD c.val 0,?_⟩
  have h := packetCheck_sound 243 false 0 packetData0282 packetPass0282 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_244 (c : Fin 32) : ∃w,BaseWitnessCheck 244 c.val false w := by
  refine ⟨packetData0283.getD c.val 0,?_⟩
  have h := packetCheck_sound 244 false 0 packetData0283 packetPass0283 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_245 (c : Fin 32) : ∃w,BaseWitnessCheck 245 c.val false w := by
  refine ⟨packetData0284.getD c.val 0,?_⟩
  have h := packetCheck_sound 245 false 0 packetData0284 packetPass0284 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_246 (c : Fin 32) : ∃w,BaseWitnessCheck 246 c.val false w := by
  refine ⟨packetData0285.getD c.val 0,?_⟩
  have h := packetCheck_sound 246 false 0 packetData0285 packetPass0285 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_247 (c : Fin 32) : ∃w,BaseWitnessCheck 247 c.val false w := by
  refine ⟨packetData0286.getD c.val 0,?_⟩
  have h := packetCheck_sound 247 false 0 packetData0286 packetPass0286 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_248 (c : Fin 32) : ∃w,BaseWitnessCheck 248 c.val false w := by
  refine ⟨packetData0016.getD c.val 0,?_⟩
  have h := packetCheck_sound 248 false 0 packetData0016 packetPass0016 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_249 (c : Fin 32) : ∃w,BaseWitnessCheck 249 c.val false w := by
  refine ⟨packetData0017.getD c.val 0,?_⟩
  have h := packetCheck_sound 249 false 0 packetData0017 packetPass0017 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_250 (c : Fin 32) : ∃w,BaseWitnessCheck 250 c.val false w := by
  refine ⟨packetData0018.getD c.val 0,?_⟩
  have h := packetCheck_sound 250 false 0 packetData0018 packetPass0018 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_251 (c : Fin 32) : ∃w,BaseWitnessCheck 251 c.val false w := by
  refine ⟨packetData0019.getD c.val 0,?_⟩
  have h := packetCheck_sound 251 false 0 packetData0019 packetPass0019 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_252 (c : Fin 32) : ∃w,BaseWitnessCheck 252 c.val false w := by
  refine ⟨packetData0287.getD c.val 0,?_⟩
  have h := packetCheck_sound 252 false 0 packetData0287 packetPass0287 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_253 (c : Fin 32) : ∃w,BaseWitnessCheck 253 c.val false w := by
  refine ⟨packetData0288.getD c.val 0,?_⟩
  have h := packetCheck_sound 253 false 0 packetData0288 packetPass0288 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_254 (c : Fin 32) : ∃w,BaseWitnessCheck 254 c.val false w := by
  refine ⟨packetData0289.getD c.val 0,?_⟩
  have h := packetCheck_sound 254 false 0 packetData0289 packetPass0289 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_255 (c : Fin 32) : ∃w,BaseWitnessCheck 255 c.val false w := by
  refine ⟨packetData0290.getD c.val 0,?_⟩
  have h := packetCheck_sound 255 false 0 packetData0290 packetPass0290 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_256 (c : Fin 32) : ∃w,BaseWitnessCheck 256 c.val false w := by
  refine ⟨packetData0291.getD c.val 0,?_⟩
  have h := packetCheck_sound 256 false 0 packetData0291 packetPass0291 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_257 (c : Fin 32) : ∃w,BaseWitnessCheck 257 c.val false w := by
  refine ⟨packetData0292.getD c.val 0,?_⟩
  have h := packetCheck_sound 257 false 0 packetData0292 packetPass0292 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_258 (c : Fin 32) : ∃w,BaseWitnessCheck 258 c.val false w := by
  refine ⟨packetData0293.getD c.val 0,?_⟩
  have h := packetCheck_sound 258 false 0 packetData0293 packetPass0293 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_259 (c : Fin 32) : ∃w,BaseWitnessCheck 259 c.val false w := by
  refine ⟨packetData0294.getD c.val 0,?_⟩
  have h := packetCheck_sound 259 false 0 packetData0294 packetPass0294 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_260 (c : Fin 32) : ∃w,BaseWitnessCheck 260 c.val false w := by
  refine ⟨packetData0295.getD c.val 0,?_⟩
  have h := packetCheck_sound 260 false 0 packetData0295 packetPass0295 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_261 (c : Fin 32) : ∃w,BaseWitnessCheck 261 c.val false w := by
  refine ⟨packetData0296.getD c.val 0,?_⟩
  have h := packetCheck_sound 261 false 0 packetData0296 packetPass0296 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_262 (c : Fin 32) : ∃w,BaseWitnessCheck 262 c.val false w := by
  refine ⟨packetData0297.getD c.val 0,?_⟩
  have h := packetCheck_sound 262 false 0 packetData0297 packetPass0297 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_263 (c : Fin 32) : ∃w,BaseWitnessCheck 263 c.val false w := by
  refine ⟨packetData0298.getD c.val 0,?_⟩
  have h := packetCheck_sound 263 false 0 packetData0298 packetPass0298 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_264 (c : Fin 32) : ∃w,BaseWitnessCheck 264 c.val false w := by
  refine ⟨packetData0299.getD c.val 0,?_⟩
  have h := packetCheck_sound 264 false 0 packetData0299 packetPass0299 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_265 (c : Fin 32) : ∃w,BaseWitnessCheck 265 c.val false w := by
  refine ⟨packetData0300.getD c.val 0,?_⟩
  have h := packetCheck_sound 265 false 0 packetData0300 packetPass0300 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_266 (c : Fin 32) : ∃w,BaseWitnessCheck 266 c.val false w := by
  refine ⟨packetData0301.getD c.val 0,?_⟩
  have h := packetCheck_sound 266 false 0 packetData0301 packetPass0301 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_267 (c : Fin 32) : ∃w,BaseWitnessCheck 267 c.val false w := by
  refine ⟨packetData0302.getD c.val 0,?_⟩
  have h := packetCheck_sound 267 false 0 packetData0302 packetPass0302 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_268 (c : Fin 32) : ∃w,BaseWitnessCheck 268 c.val false w := by
  refine ⟨packetData0303.getD c.val 0,?_⟩
  have h := packetCheck_sound 268 false 0 packetData0303 packetPass0303 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_269 (c : Fin 32) : ∃w,BaseWitnessCheck 269 c.val false w := by
  refine ⟨packetData0304.getD c.val 0,?_⟩
  have h := packetCheck_sound 269 false 0 packetData0304 packetPass0304 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_270 (c : Fin 32) : ∃w,BaseWitnessCheck 270 c.val false w := by
  refine ⟨packetData0305.getD c.val 0,?_⟩
  have h := packetCheck_sound 270 false 0 packetData0305 packetPass0305 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_271 (c : Fin 32) : ∃w,BaseWitnessCheck 271 c.val false w := by
  refine ⟨packetData0306.getD c.val 0,?_⟩
  have h := packetCheck_sound 271 false 0 packetData0306 packetPass0306 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_272 (c : Fin 32) : ∃w,BaseWitnessCheck 272 c.val false w := by
  refine ⟨packetData0307.getD c.val 0,?_⟩
  have h := packetCheck_sound 272 false 0 packetData0307 packetPass0307 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_273 (c : Fin 32) : ∃w,BaseWitnessCheck 273 c.val false w := by
  refine ⟨packetData0308.getD c.val 0,?_⟩
  have h := packetCheck_sound 273 false 0 packetData0308 packetPass0308 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_274 (c : Fin 32) : ∃w,BaseWitnessCheck 274 c.val false w := by
  refine ⟨packetData0309.getD c.val 0,?_⟩
  have h := packetCheck_sound 274 false 0 packetData0309 packetPass0309 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_0_275 (c : Fin 32) : ∃w,BaseWitnessCheck 275 c.val false w := by
  refine ⟨packetData0310.getD c.val 0,?_⟩
  have h := packetCheck_sound 275 false 0 packetData0310 packetPass0310 c.val c.isLt
  simpa only [Nat.zero_add] using h

 def packets_0_276 : Fin 8 → Array Nat := ![packetData0311,packetData0312,packetData0313,packetData0314,packetData0315,packetData0316,packetData0317,packetData0318]
 theorem packets_size_0_276 : ∀p,(packets_0_276 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_276 : ∀p,packetCheck 276 false (p.val*64) (packets_0_276 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0311
  · exact packetPass0312
  · exact packetPass0313
  · exact packetPass0314
  · exact packetPass0315
  · exact packetPass0316
  · exact packetPass0317
  · exact packetPass0318
 theorem covered_0_276 (c : Fin 512) : ∃w,BaseWitnessCheck 276 c.val false w :=
  packet_coverage 276 false 512 8 rfl packets_0_276 packets_size_0_276 packets_pass_0_276 c

 def packets_0_277 : Fin 8 → Array Nat := ![packetData0319,packetData0320,packetData0321,packetData0322,packetData0323,packetData0324,packetData0325,packetData0326]
 theorem packets_size_0_277 : ∀p,(packets_0_277 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_277 : ∀p,packetCheck 277 false (p.val*64) (packets_0_277 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0319
  · exact packetPass0320
  · exact packetPass0321
  · exact packetPass0322
  · exact packetPass0323
  · exact packetPass0324
  · exact packetPass0325
  · exact packetPass0326
 theorem covered_0_277 (c : Fin 512) : ∃w,BaseWitnessCheck 277 c.val false w :=
  packet_coverage 277 false 512 8 rfl packets_0_277 packets_size_0_277 packets_pass_0_277 c

 def packets_0_278 : Fin 8 → Array Nat := ![packetData0327,packetData0328,packetData0329,packetData0330,packetData0331,packetData0332,packetData0333,packetData0334]
 theorem packets_size_0_278 : ∀p,(packets_0_278 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_278 : ∀p,packetCheck 278 false (p.val*64) (packets_0_278 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0327
  · exact packetPass0328
  · exact packetPass0329
  · exact packetPass0330
  · exact packetPass0331
  · exact packetPass0332
  · exact packetPass0333
  · exact packetPass0334
 theorem covered_0_278 (c : Fin 512) : ∃w,BaseWitnessCheck 278 c.val false w :=
  packet_coverage 278 false 512 8 rfl packets_0_278 packets_size_0_278 packets_pass_0_278 c

 def packets_0_279 : Fin 8 → Array Nat := ![packetData0335,packetData0336,packetData0337,packetData0338,packetData0339,packetData0340,packetData0341,packetData0342]
 theorem packets_size_0_279 : ∀p,(packets_0_279 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_279 : ∀p,packetCheck 279 false (p.val*64) (packets_0_279 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0335
  · exact packetPass0336
  · exact packetPass0337
  · exact packetPass0338
  · exact packetPass0339
  · exact packetPass0340
  · exact packetPass0341
  · exact packetPass0342
 theorem covered_0_279 (c : Fin 512) : ∃w,BaseWitnessCheck 279 c.val false w :=
  packet_coverage 279 false 512 8 rfl packets_0_279 packets_size_0_279 packets_pass_0_279 c

 def packets_0_280 : Fin 8 → Array Nat := ![packetData0343,packetData0344,packetData0345,packetData0346,packetData0347,packetData0348,packetData0349,packetData0350]
 theorem packets_size_0_280 : ∀p,(packets_0_280 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_280 : ∀p,packetCheck 280 false (p.val*64) (packets_0_280 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0343
  · exact packetPass0344
  · exact packetPass0345
  · exact packetPass0346
  · exact packetPass0347
  · exact packetPass0348
  · exact packetPass0349
  · exact packetPass0350
 theorem covered_0_280 (c : Fin 512) : ∃w,BaseWitnessCheck 280 c.val false w :=
  packet_coverage 280 false 512 8 rfl packets_0_280 packets_size_0_280 packets_pass_0_280 c

 def packets_0_281 : Fin 8 → Array Nat := ![packetData0351,packetData0352,packetData0353,packetData0354,packetData0355,packetData0356,packetData0357,packetData0358]
 theorem packets_size_0_281 : ∀p,(packets_0_281 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_281 : ∀p,packetCheck 281 false (p.val*64) (packets_0_281 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0351
  · exact packetPass0352
  · exact packetPass0353
  · exact packetPass0354
  · exact packetPass0355
  · exact packetPass0356
  · exact packetPass0357
  · exact packetPass0358
 theorem covered_0_281 (c : Fin 512) : ∃w,BaseWitnessCheck 281 c.val false w :=
  packet_coverage 281 false 512 8 rfl packets_0_281 packets_size_0_281 packets_pass_0_281 c

 def packets_0_282 : Fin 8 → Array Nat := ![packetData0359,packetData0360,packetData0361,packetData0362,packetData0363,packetData0364,packetData0365,packetData0366]
 theorem packets_size_0_282 : ∀p,(packets_0_282 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_282 : ∀p,packetCheck 282 false (p.val*64) (packets_0_282 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0359
  · exact packetPass0360
  · exact packetPass0361
  · exact packetPass0362
  · exact packetPass0363
  · exact packetPass0364
  · exact packetPass0365
  · exact packetPass0366
 theorem covered_0_282 (c : Fin 512) : ∃w,BaseWitnessCheck 282 c.val false w :=
  packet_coverage 282 false 512 8 rfl packets_0_282 packets_size_0_282 packets_pass_0_282 c

 def packets_0_283 : Fin 8 → Array Nat := ![packetData0367,packetData0368,packetData0369,packetData0370,packetData0371,packetData0372,packetData0373,packetData0374]
 theorem packets_size_0_283 : ∀p,(packets_0_283 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_283 : ∀p,packetCheck 283 false (p.val*64) (packets_0_283 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0367
  · exact packetPass0368
  · exact packetPass0369
  · exact packetPass0370
  · exact packetPass0371
  · exact packetPass0372
  · exact packetPass0373
  · exact packetPass0374
 theorem covered_0_283 (c : Fin 512) : ∃w,BaseWitnessCheck 283 c.val false w :=
  packet_coverage 283 false 512 8 rfl packets_0_283 packets_size_0_283 packets_pass_0_283 c

 def packets_0_284 : Fin 8 → Array Nat := ![packetData0375,packetData0376,packetData0377,packetData0378,packetData0379,packetData0380,packetData0381,packetData0382]
 theorem packets_size_0_284 : ∀p,(packets_0_284 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_284 : ∀p,packetCheck 284 false (p.val*64) (packets_0_284 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0375
  · exact packetPass0376
  · exact packetPass0377
  · exact packetPass0378
  · exact packetPass0379
  · exact packetPass0380
  · exact packetPass0381
  · exact packetPass0382
 theorem covered_0_284 (c : Fin 512) : ∃w,BaseWitnessCheck 284 c.val false w :=
  packet_coverage 284 false 512 8 rfl packets_0_284 packets_size_0_284 packets_pass_0_284 c

 def packets_0_285 : Fin 8 → Array Nat := ![packetData0383,packetData0384,packetData0385,packetData0386,packetData0387,packetData0388,packetData0389,packetData0390]
 theorem packets_size_0_285 : ∀p,(packets_0_285 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_285 : ∀p,packetCheck 285 false (p.val*64) (packets_0_285 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0383
  · exact packetPass0384
  · exact packetPass0385
  · exact packetPass0386
  · exact packetPass0387
  · exact packetPass0388
  · exact packetPass0389
  · exact packetPass0390
 theorem covered_0_285 (c : Fin 512) : ∃w,BaseWitnessCheck 285 c.val false w :=
  packet_coverage 285 false 512 8 rfl packets_0_285 packets_size_0_285 packets_pass_0_285 c

 def packets_0_286 : Fin 8 → Array Nat := ![packetData0391,packetData0392,packetData0393,packetData0394,packetData0395,packetData0396,packetData0397,packetData0398]
 theorem packets_size_0_286 : ∀p,(packets_0_286 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_286 : ∀p,packetCheck 286 false (p.val*64) (packets_0_286 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0391
  · exact packetPass0392
  · exact packetPass0393
  · exact packetPass0394
  · exact packetPass0395
  · exact packetPass0396
  · exact packetPass0397
  · exact packetPass0398
 theorem covered_0_286 (c : Fin 512) : ∃w,BaseWitnessCheck 286 c.val false w :=
  packet_coverage 286 false 512 8 rfl packets_0_286 packets_size_0_286 packets_pass_0_286 c

 def packets_0_287 : Fin 8 → Array Nat := ![packetData0399,packetData0400,packetData0401,packetData0402,packetData0403,packetData0404,packetData0405,packetData0406]
 theorem packets_size_0_287 : ∀p,(packets_0_287 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_287 : ∀p,packetCheck 287 false (p.val*64) (packets_0_287 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0399
  · exact packetPass0400
  · exact packetPass0401
  · exact packetPass0402
  · exact packetPass0403
  · exact packetPass0404
  · exact packetPass0405
  · exact packetPass0406
 theorem covered_0_287 (c : Fin 512) : ∃w,BaseWitnessCheck 287 c.val false w :=
  packet_coverage 287 false 512 8 rfl packets_0_287 packets_size_0_287 packets_pass_0_287 c

 def packets_0_288 : Fin 8 → Array Nat := ![packetData0407,packetData0408,packetData0409,packetData0410,packetData0411,packetData0412,packetData0413,packetData0414]
 theorem packets_size_0_288 : ∀p,(packets_0_288 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_288 : ∀p,packetCheck 288 false (p.val*64) (packets_0_288 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0407
  · exact packetPass0408
  · exact packetPass0409
  · exact packetPass0410
  · exact packetPass0411
  · exact packetPass0412
  · exact packetPass0413
  · exact packetPass0414
 theorem covered_0_288 (c : Fin 512) : ∃w,BaseWitnessCheck 288 c.val false w :=
  packet_coverage 288 false 512 8 rfl packets_0_288 packets_size_0_288 packets_pass_0_288 c

 def packets_0_289 : Fin 8 → Array Nat := ![packetData0415,packetData0416,packetData0417,packetData0418,packetData0419,packetData0420,packetData0421,packetData0422]
 theorem packets_size_0_289 : ∀p,(packets_0_289 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_289 : ∀p,packetCheck 289 false (p.val*64) (packets_0_289 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0415
  · exact packetPass0416
  · exact packetPass0417
  · exact packetPass0418
  · exact packetPass0419
  · exact packetPass0420
  · exact packetPass0421
  · exact packetPass0422
 theorem covered_0_289 (c : Fin 512) : ∃w,BaseWitnessCheck 289 c.val false w :=
  packet_coverage 289 false 512 8 rfl packets_0_289 packets_size_0_289 packets_pass_0_289 c

 def packets_0_290 : Fin 8 → Array Nat := ![packetData0423,packetData0424,packetData0425,packetData0426,packetData0427,packetData0428,packetData0429,packetData0430]
 theorem packets_size_0_290 : ∀p,(packets_0_290 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_290 : ∀p,packetCheck 290 false (p.val*64) (packets_0_290 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0423
  · exact packetPass0424
  · exact packetPass0425
  · exact packetPass0426
  · exact packetPass0427
  · exact packetPass0428
  · exact packetPass0429
  · exact packetPass0430
 theorem covered_0_290 (c : Fin 512) : ∃w,BaseWitnessCheck 290 c.val false w :=
  packet_coverage 290 false 512 8 rfl packets_0_290 packets_size_0_290 packets_pass_0_290 c

 def packets_0_291 : Fin 8 → Array Nat := ![packetData0431,packetData0432,packetData0433,packetData0434,packetData0435,packetData0436,packetData0437,packetData0438]
 theorem packets_size_0_291 : ∀p,(packets_0_291 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_291 : ∀p,packetCheck 291 false (p.val*64) (packets_0_291 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0431
  · exact packetPass0432
  · exact packetPass0433
  · exact packetPass0434
  · exact packetPass0435
  · exact packetPass0436
  · exact packetPass0437
  · exact packetPass0438
 theorem covered_0_291 (c : Fin 512) : ∃w,BaseWitnessCheck 291 c.val false w :=
  packet_coverage 291 false 512 8 rfl packets_0_291 packets_size_0_291 packets_pass_0_291 c

 def packets_0_292 : Fin 8 → Array Nat := ![packetData0439,packetData0440,packetData0441,packetData0442,packetData0443,packetData0444,packetData0445,packetData0446]
 theorem packets_size_0_292 : ∀p,(packets_0_292 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_292 : ∀p,packetCheck 292 false (p.val*64) (packets_0_292 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0439
  · exact packetPass0440
  · exact packetPass0441
  · exact packetPass0442
  · exact packetPass0443
  · exact packetPass0444
  · exact packetPass0445
  · exact packetPass0446
 theorem covered_0_292 (c : Fin 512) : ∃w,BaseWitnessCheck 292 c.val false w :=
  packet_coverage 292 false 512 8 rfl packets_0_292 packets_size_0_292 packets_pass_0_292 c

 def packets_0_293 : Fin 8 → Array Nat := ![packetData0447,packetData0448,packetData0449,packetData0450,packetData0451,packetData0452,packetData0453,packetData0454]
 theorem packets_size_0_293 : ∀p,(packets_0_293 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_293 : ∀p,packetCheck 293 false (p.val*64) (packets_0_293 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0447
  · exact packetPass0448
  · exact packetPass0449
  · exact packetPass0450
  · exact packetPass0451
  · exact packetPass0452
  · exact packetPass0453
  · exact packetPass0454
 theorem covered_0_293 (c : Fin 512) : ∃w,BaseWitnessCheck 293 c.val false w :=
  packet_coverage 293 false 512 8 rfl packets_0_293 packets_size_0_293 packets_pass_0_293 c

 def packets_0_294 : Fin 8 → Array Nat := ![packetData0455,packetData0456,packetData0457,packetData0458,packetData0459,packetData0460,packetData0461,packetData0462]
 theorem packets_size_0_294 : ∀p,(packets_0_294 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_294 : ∀p,packetCheck 294 false (p.val*64) (packets_0_294 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0455
  · exact packetPass0456
  · exact packetPass0457
  · exact packetPass0458
  · exact packetPass0459
  · exact packetPass0460
  · exact packetPass0461
  · exact packetPass0462
 theorem covered_0_294 (c : Fin 512) : ∃w,BaseWitnessCheck 294 c.val false w :=
  packet_coverage 294 false 512 8 rfl packets_0_294 packets_size_0_294 packets_pass_0_294 c

 def packets_0_295 : Fin 8 → Array Nat := ![packetData0463,packetData0464,packetData0465,packetData0466,packetData0467,packetData0468,packetData0469,packetData0470]
 theorem packets_size_0_295 : ∀p,(packets_0_295 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_295 : ∀p,packetCheck 295 false (p.val*64) (packets_0_295 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0463
  · exact packetPass0464
  · exact packetPass0465
  · exact packetPass0466
  · exact packetPass0467
  · exact packetPass0468
  · exact packetPass0469
  · exact packetPass0470
 theorem covered_0_295 (c : Fin 512) : ∃w,BaseWitnessCheck 295 c.val false w :=
  packet_coverage 295 false 512 8 rfl packets_0_295 packets_size_0_295 packets_pass_0_295 c

 def packets_0_296 : Fin 8 → Array Nat := ![packetData0471,packetData0472,packetData0473,packetData0474,packetData0475,packetData0476,packetData0477,packetData0478]
 theorem packets_size_0_296 : ∀p,(packets_0_296 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_296 : ∀p,packetCheck 296 false (p.val*64) (packets_0_296 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0471
  · exact packetPass0472
  · exact packetPass0473
  · exact packetPass0474
  · exact packetPass0475
  · exact packetPass0476
  · exact packetPass0477
  · exact packetPass0478
 theorem covered_0_296 (c : Fin 512) : ∃w,BaseWitnessCheck 296 c.val false w :=
  packet_coverage 296 false 512 8 rfl packets_0_296 packets_size_0_296 packets_pass_0_296 c

 def packets_0_297 : Fin 8 → Array Nat := ![packetData0479,packetData0480,packetData0481,packetData0482,packetData0483,packetData0484,packetData0485,packetData0486]
 theorem packets_size_0_297 : ∀p,(packets_0_297 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_297 : ∀p,packetCheck 297 false (p.val*64) (packets_0_297 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0479
  · exact packetPass0480
  · exact packetPass0481
  · exact packetPass0482
  · exact packetPass0483
  · exact packetPass0484
  · exact packetPass0485
  · exact packetPass0486
 theorem covered_0_297 (c : Fin 512) : ∃w,BaseWitnessCheck 297 c.val false w :=
  packet_coverage 297 false 512 8 rfl packets_0_297 packets_size_0_297 packets_pass_0_297 c

 def packets_0_298 : Fin 8 → Array Nat := ![packetData0487,packetData0488,packetData0489,packetData0490,packetData0491,packetData0492,packetData0493,packetData0494]
 theorem packets_size_0_298 : ∀p,(packets_0_298 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_298 : ∀p,packetCheck 298 false (p.val*64) (packets_0_298 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0487
  · exact packetPass0488
  · exact packetPass0489
  · exact packetPass0490
  · exact packetPass0491
  · exact packetPass0492
  · exact packetPass0493
  · exact packetPass0494
 theorem covered_0_298 (c : Fin 512) : ∃w,BaseWitnessCheck 298 c.val false w :=
  packet_coverage 298 false 512 8 rfl packets_0_298 packets_size_0_298 packets_pass_0_298 c

 def packets_0_299 : Fin 8 → Array Nat := ![packetData0495,packetData0496,packetData0497,packetData0498,packetData0499,packetData0500,packetData0501,packetData0502]
 theorem packets_size_0_299 : ∀p,(packets_0_299 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_299 : ∀p,packetCheck 299 false (p.val*64) (packets_0_299 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0495
  · exact packetPass0496
  · exact packetPass0497
  · exact packetPass0498
  · exact packetPass0499
  · exact packetPass0500
  · exact packetPass0501
  · exact packetPass0502
 theorem covered_0_299 (c : Fin 512) : ∃w,BaseWitnessCheck 299 c.val false w :=
  packet_coverage 299 false 512 8 rfl packets_0_299 packets_size_0_299 packets_pass_0_299 c

 def packets_0_300 : Fin 8 → Array Nat := ![packetData0503,packetData0504,packetData0505,packetData0506,packetData0507,packetData0508,packetData0509,packetData0510]
 theorem packets_size_0_300 : ∀p,(packets_0_300 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_300 : ∀p,packetCheck 300 false (p.val*64) (packets_0_300 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0503
  · exact packetPass0504
  · exact packetPass0505
  · exact packetPass0506
  · exact packetPass0507
  · exact packetPass0508
  · exact packetPass0509
  · exact packetPass0510
 theorem covered_0_300 (c : Fin 512) : ∃w,BaseWitnessCheck 300 c.val false w :=
  packet_coverage 300 false 512 8 rfl packets_0_300 packets_size_0_300 packets_pass_0_300 c

 def packets_0_301 : Fin 8 → Array Nat := ![packetData0511,packetData0512,packetData0513,packetData0514,packetData0515,packetData0516,packetData0517,packetData0518]
 theorem packets_size_0_301 : ∀p,(packets_0_301 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_301 : ∀p,packetCheck 301 false (p.val*64) (packets_0_301 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0511
  · exact packetPass0512
  · exact packetPass0513
  · exact packetPass0514
  · exact packetPass0515
  · exact packetPass0516
  · exact packetPass0517
  · exact packetPass0518
 theorem covered_0_301 (c : Fin 512) : ∃w,BaseWitnessCheck 301 c.val false w :=
  packet_coverage 301 false 512 8 rfl packets_0_301 packets_size_0_301 packets_pass_0_301 c

 def packets_0_302 : Fin 8 → Array Nat := ![packetData0519,packetData0520,packetData0521,packetData0522,packetData0523,packetData0524,packetData0525,packetData0526]
 theorem packets_size_0_302 : ∀p,(packets_0_302 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_302 : ∀p,packetCheck 302 false (p.val*64) (packets_0_302 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0519
  · exact packetPass0520
  · exact packetPass0521
  · exact packetPass0522
  · exact packetPass0523
  · exact packetPass0524
  · exact packetPass0525
  · exact packetPass0526
 theorem covered_0_302 (c : Fin 512) : ∃w,BaseWitnessCheck 302 c.val false w :=
  packet_coverage 302 false 512 8 rfl packets_0_302 packets_size_0_302 packets_pass_0_302 c

 def packets_0_303 : Fin 8 → Array Nat := ![packetData0527,packetData0528,packetData0529,packetData0530,packetData0531,packetData0532,packetData0533,packetData0534]
 theorem packets_size_0_303 : ∀p,(packets_0_303 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_303 : ∀p,packetCheck 303 false (p.val*64) (packets_0_303 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0527
  · exact packetPass0528
  · exact packetPass0529
  · exact packetPass0530
  · exact packetPass0531
  · exact packetPass0532
  · exact packetPass0533
  · exact packetPass0534
 theorem covered_0_303 (c : Fin 512) : ∃w,BaseWitnessCheck 303 c.val false w :=
  packet_coverage 303 false 512 8 rfl packets_0_303 packets_size_0_303 packets_pass_0_303 c

 def packets_0_304 : Fin 8 → Array Nat := ![packetData0535,packetData0536,packetData0537,packetData0538,packetData0539,packetData0540,packetData0541,packetData0542]
 theorem packets_size_0_304 : ∀p,(packets_0_304 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_304 : ∀p,packetCheck 304 false (p.val*64) (packets_0_304 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0535
  · exact packetPass0536
  · exact packetPass0537
  · exact packetPass0538
  · exact packetPass0539
  · exact packetPass0540
  · exact packetPass0541
  · exact packetPass0542
 theorem covered_0_304 (c : Fin 512) : ∃w,BaseWitnessCheck 304 c.val false w :=
  packet_coverage 304 false 512 8 rfl packets_0_304 packets_size_0_304 packets_pass_0_304 c

 def packets_0_305 : Fin 8 → Array Nat := ![packetData0543,packetData0544,packetData0545,packetData0546,packetData0547,packetData0548,packetData0549,packetData0550]
 theorem packets_size_0_305 : ∀p,(packets_0_305 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_305 : ∀p,packetCheck 305 false (p.val*64) (packets_0_305 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0543
  · exact packetPass0544
  · exact packetPass0545
  · exact packetPass0546
  · exact packetPass0547
  · exact packetPass0548
  · exact packetPass0549
  · exact packetPass0550
 theorem covered_0_305 (c : Fin 512) : ∃w,BaseWitnessCheck 305 c.val false w :=
  packet_coverage 305 false 512 8 rfl packets_0_305 packets_size_0_305 packets_pass_0_305 c

 def packets_0_306 : Fin 256 → Array Nat := ![packetData0551,packetData0552,packetData0553,packetData0554,packetData0555,packetData0556,packetData0557,packetData0558,packetData0559,packetData0560,packetData0561,packetData0562,packetData0563,packetData0564,packetData0565,packetData0566,packetData0567,packetData0568,packetData0569,packetData0570,packetData0571,packetData0572,packetData0573,packetData0574,packetData0575,packetData0576,packetData0577,packetData0578,packetData0579,packetData0580,packetData0581,packetData0582,packetData0583,packetData0584,packetData0585,packetData0586,packetData0587,packetData0588,packetData0589,packetData0590,packetData0591,packetData0592,packetData0593,packetData0594,packetData0595,packetData0596,packetData0597,packetData0598,packetData0599,packetData0600,packetData0601,packetData0602,packetData0603,packetData0604,packetData0605,packetData0606,packetData0607,packetData0608,packetData0609,packetData0610,packetData0611,packetData0612,packetData0613,packetData0614,packetData0615,packetData0616,packetData0617,packetData0618,packetData0619,packetData0620,packetData0621,packetData0622,packetData0623,packetData0624,packetData0625,packetData0626,packetData0627,packetData0628,packetData0629,packetData0630,packetData0631,packetData0632,packetData0633,packetData0634,packetData0635,packetData0636,packetData0637,packetData0638,packetData0639,packetData0640,packetData0641,packetData0642,packetData0643,packetData0644,packetData0645,packetData0646,packetData0647,packetData0648,packetData0649,packetData0650,packetData0651,packetData0652,packetData0653,packetData0654,packetData0655,packetData0656,packetData0657,packetData0658,packetData0659,packetData0660,packetData0661,packetData0662,packetData0663,packetData0664,packetData0665,packetData0666,packetData0667,packetData0668,packetData0669,packetData0670,packetData0671,packetData0672,packetData0673,packetData0674,packetData0675,packetData0676,packetData0677,packetData0678,packetData0679,packetData0680,packetData0681,packetData0682,packetData0683,packetData0684,packetData0685,packetData0686,packetData0687,packetData0688,packetData0689,packetData0690,packetData0691,packetData0692,packetData0693,packetData0694,packetData0695,packetData0696,packetData0697,packetData0698,packetData0699,packetData0700,packetData0701,packetData0702,packetData0703,packetData0704,packetData0705,packetData0706,packetData0707,packetData0708,packetData0709,packetData0710,packetData0711,packetData0712,packetData0713,packetData0714,packetData0715,packetData0716,packetData0717,packetData0718,packetData0719,packetData0720,packetData0721,packetData0722,packetData0723,packetData0724,packetData0725,packetData0726,packetData0727,packetData0728,packetData0729,packetData0730,packetData0731,packetData0732,packetData0733,packetData0734,packetData0735,packetData0736,packetData0737,packetData0738,packetData0739,packetData0740,packetData0741,packetData0742,packetData0743,packetData0744,packetData0745,packetData0746,packetData0747,packetData0748,packetData0749,packetData0750,packetData0751,packetData0752,packetData0753,packetData0754,packetData0755,packetData0756,packetData0757,packetData0758,packetData0759,packetData0760,packetData0761,packetData0762,packetData0763,packetData0764,packetData0765,packetData0766,packetData0767,packetData0768,packetData0769,packetData0770,packetData0771,packetData0772,packetData0773,packetData0774,packetData0775,packetData0776,packetData0777,packetData0778,packetData0779,packetData0780,packetData0781,packetData0782,packetData0783,packetData0784,packetData0785,packetData0786,packetData0787,packetData0788,packetData0789,packetData0790,packetData0791,packetData0792,packetData0793,packetData0794,packetData0795,packetData0796,packetData0797,packetData0798,packetData0799,packetData0800,packetData0801,packetData0802,packetData0803,packetData0804,packetData0805,packetData0806]
 theorem packets_size_0_306 : ∀p,(packets_0_306 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_0_306 : ∀p,packetCheck 306 false (p.val*64) (packets_0_306 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0551
  · exact packetPass0552
  · exact packetPass0553
  · exact packetPass0554
  · exact packetPass0555
  · exact packetPass0556
  · exact packetPass0557
  · exact packetPass0558
  · exact packetPass0559
  · exact packetPass0560
  · exact packetPass0561
  · exact packetPass0562
  · exact packetPass0563
  · exact packetPass0564
  · exact packetPass0565
  · exact packetPass0566
  · exact packetPass0567
  · exact packetPass0568
  · exact packetPass0569
  · exact packetPass0570
  · exact packetPass0571
  · exact packetPass0572
  · exact packetPass0573
  · exact packetPass0574
  · exact packetPass0575
  · exact packetPass0576
  · exact packetPass0577
  · exact packetPass0578
  · exact packetPass0579
  · exact packetPass0580
  · exact packetPass0581
  · exact packetPass0582
  · exact packetPass0583
  · exact packetPass0584
  · exact packetPass0585
  · exact packetPass0586
  · exact packetPass0587
  · exact packetPass0588
  · exact packetPass0589
  · exact packetPass0590
  · exact packetPass0591
  · exact packetPass0592
  · exact packetPass0593
  · exact packetPass0594
  · exact packetPass0595
  · exact packetPass0596
  · exact packetPass0597
  · exact packetPass0598
  · exact packetPass0599
  · exact packetPass0600
  · exact packetPass0601
  · exact packetPass0602
  · exact packetPass0603
  · exact packetPass0604
  · exact packetPass0605
  · exact packetPass0606
  · exact packetPass0607
  · exact packetPass0608
  · exact packetPass0609
  · exact packetPass0610
  · exact packetPass0611
  · exact packetPass0612
  · exact packetPass0613
  · exact packetPass0614
  · exact packetPass0615
  · exact packetPass0616
  · exact packetPass0617
  · exact packetPass0618
  · exact packetPass0619
  · exact packetPass0620
  · exact packetPass0621
  · exact packetPass0622
  · exact packetPass0623
  · exact packetPass0624
  · exact packetPass0625
  · exact packetPass0626
  · exact packetPass0627
  · exact packetPass0628
  · exact packetPass0629
  · exact packetPass0630
  · exact packetPass0631
  · exact packetPass0632
  · exact packetPass0633
  · exact packetPass0634
  · exact packetPass0635
  · exact packetPass0636
  · exact packetPass0637
  · exact packetPass0638
  · exact packetPass0639
  · exact packetPass0640
  · exact packetPass0641
  · exact packetPass0642
  · exact packetPass0643
  · exact packetPass0644
  · exact packetPass0645
  · exact packetPass0646
  · exact packetPass0647
  · exact packetPass0648
  · exact packetPass0649
  · exact packetPass0650
  · exact packetPass0651
  · exact packetPass0652
  · exact packetPass0653
  · exact packetPass0654
  · exact packetPass0655
  · exact packetPass0656
  · exact packetPass0657
  · exact packetPass0658
  · exact packetPass0659
  · exact packetPass0660
  · exact packetPass0661
  · exact packetPass0662
  · exact packetPass0663
  · exact packetPass0664
  · exact packetPass0665
  · exact packetPass0666
  · exact packetPass0667
  · exact packetPass0668
  · exact packetPass0669
  · exact packetPass0670
  · exact packetPass0671
  · exact packetPass0672
  · exact packetPass0673
  · exact packetPass0674
  · exact packetPass0675
  · exact packetPass0676
  · exact packetPass0677
  · exact packetPass0678
  · exact packetPass0679
  · exact packetPass0680
  · exact packetPass0681
  · exact packetPass0682
  · exact packetPass0683
  · exact packetPass0684
  · exact packetPass0685
  · exact packetPass0686
  · exact packetPass0687
  · exact packetPass0688
  · exact packetPass0689
  · exact packetPass0690
  · exact packetPass0691
  · exact packetPass0692
  · exact packetPass0693
  · exact packetPass0694
  · exact packetPass0695
  · exact packetPass0696
  · exact packetPass0697
  · exact packetPass0698
  · exact packetPass0699
  · exact packetPass0700
  · exact packetPass0701
  · exact packetPass0702
  · exact packetPass0703
  · exact packetPass0704
  · exact packetPass0705
  · exact packetPass0706
  · exact packetPass0707
  · exact packetPass0708
  · exact packetPass0709
  · exact packetPass0710
  · exact packetPass0711
  · exact packetPass0712
  · exact packetPass0713
  · exact packetPass0714
  · exact packetPass0715
  · exact packetPass0716
  · exact packetPass0717
  · exact packetPass0718
  · exact packetPass0719
  · exact packetPass0720
  · exact packetPass0721
  · exact packetPass0722
  · exact packetPass0723
  · exact packetPass0724
  · exact packetPass0725
  · exact packetPass0726
  · exact packetPass0727
  · exact packetPass0728
  · exact packetPass0729
  · exact packetPass0730
  · exact packetPass0731
  · exact packetPass0732
  · exact packetPass0733
  · exact packetPass0734
  · exact packetPass0735
  · exact packetPass0736
  · exact packetPass0737
  · exact packetPass0738
  · exact packetPass0739
  · exact packetPass0740
  · exact packetPass0741
  · exact packetPass0742
  · exact packetPass0743
  · exact packetPass0744
  · exact packetPass0745
  · exact packetPass0746
  · exact packetPass0747
  · exact packetPass0748
  · exact packetPass0749
  · exact packetPass0750
  · exact packetPass0751
  · exact packetPass0752
  · exact packetPass0753
  · exact packetPass0754
  · exact packetPass0755
  · exact packetPass0756
  · exact packetPass0757
  · exact packetPass0758
  · exact packetPass0759
  · exact packetPass0760
  · exact packetPass0761
  · exact packetPass0762
  · exact packetPass0763
  · exact packetPass0764
  · exact packetPass0765
  · exact packetPass0766
  · exact packetPass0767
  · exact packetPass0768
  · exact packetPass0769
  · exact packetPass0770
  · exact packetPass0771
  · exact packetPass0772
  · exact packetPass0773
  · exact packetPass0774
  · exact packetPass0775
  · exact packetPass0776
  · exact packetPass0777
  · exact packetPass0778
  · exact packetPass0779
  · exact packetPass0780
  · exact packetPass0781
  · exact packetPass0782
  · exact packetPass0783
  · exact packetPass0784
  · exact packetPass0785
  · exact packetPass0786
  · exact packetPass0787
  · exact packetPass0788
  · exact packetPass0789
  · exact packetPass0790
  · exact packetPass0791
  · exact packetPass0792
  · exact packetPass0793
  · exact packetPass0794
  · exact packetPass0795
  · exact packetPass0796
  · exact packetPass0797
  · exact packetPass0798
  · exact packetPass0799
  · exact packetPass0800
  · exact packetPass0801
  · exact packetPass0802
  · exact packetPass0803
  · exact packetPass0804
  · exact packetPass0805
  · exact packetPass0806
 theorem covered_0_306 (c : Fin 16384) : ∃w,BaseWitnessCheck 306 c.val false w :=
  packet_coverage 306 false 16384 256 rfl packets_0_306 packets_size_0_306 packets_pass_0_306 c

 theorem base_inputs_false (c : InputCode) : ∃w,BaseWitnessCheck c.1 c.2.val false w := by
  obtain ⟨s,c⟩ := c
  fin_cases s
  · exact covered_0_000 c
  · exact covered_0_001 c
  · exact covered_0_002 c
  · exact covered_0_003 c
  · exact covered_0_004 c
  · exact covered_0_005 c
  · exact covered_0_006 c
  · exact covered_0_007 c
  · exact covered_0_008 c
  · exact covered_0_009 c
  · exact covered_0_010 c
  · exact covered_0_011 c
  · exact covered_0_012 c
  · exact covered_0_013 c
  · exact covered_0_014 c
  · exact covered_0_015 c
  · exact covered_0_016 c
  · exact covered_0_017 c
  · exact covered_0_018 c
  · exact covered_0_019 c
  · exact covered_0_020 c
  · exact covered_0_021 c
  · exact covered_0_022 c
  · exact covered_0_023 c
  · exact covered_0_024 c
  · exact covered_0_025 c
  · exact covered_0_026 c
  · exact covered_0_027 c
  · exact covered_0_028 c
  · exact covered_0_029 c
  · exact covered_0_030 c
  · exact covered_0_031 c
  · exact covered_0_032 c
  · exact covered_0_033 c
  · exact covered_0_034 c
  · exact covered_0_035 c
  · exact covered_0_036 c
  · exact covered_0_037 c
  · exact covered_0_038 c
  · exact covered_0_039 c
  · exact covered_0_040 c
  · exact covered_0_041 c
  · exact covered_0_042 c
  · exact covered_0_043 c
  · exact covered_0_044 c
  · exact covered_0_045 c
  · exact covered_0_046 c
  · exact covered_0_047 c
  · exact covered_0_048 c
  · exact covered_0_049 c
  · exact covered_0_050 c
  · exact covered_0_051 c
  · exact covered_0_052 c
  · exact covered_0_053 c
  · exact covered_0_054 c
  · exact covered_0_055 c
  · exact covered_0_056 c
  · exact covered_0_057 c
  · exact covered_0_058 c
  · exact covered_0_059 c
  · exact covered_0_060 c
  · exact covered_0_061 c
  · exact covered_0_062 c
  · exact covered_0_063 c
  · exact covered_0_064 c
  · exact covered_0_065 c
  · exact covered_0_066 c
  · exact covered_0_067 c
  · exact covered_0_068 c
  · exact covered_0_069 c
  · exact covered_0_070 c
  · exact covered_0_071 c
  · exact covered_0_072 c
  · exact covered_0_073 c
  · exact covered_0_074 c
  · exact covered_0_075 c
  · exact covered_0_076 c
  · exact covered_0_077 c
  · exact covered_0_078 c
  · exact covered_0_079 c
  · exact covered_0_080 c
  · exact covered_0_081 c
  · exact covered_0_082 c
  · exact covered_0_083 c
  · exact covered_0_084 c
  · exact covered_0_085 c
  · exact covered_0_086 c
  · exact covered_0_087 c
  · exact covered_0_088 c
  · exact covered_0_089 c
  · exact covered_0_090 c
  · exact covered_0_091 c
  · exact covered_0_092 c
  · exact covered_0_093 c
  · exact covered_0_094 c
  · exact covered_0_095 c
  · exact covered_0_096 c
  · exact covered_0_097 c
  · exact covered_0_098 c
  · exact covered_0_099 c
  · exact covered_0_100 c
  · exact covered_0_101 c
  · exact covered_0_102 c
  · exact covered_0_103 c
  · exact covered_0_104 c
  · exact covered_0_105 c
  · exact covered_0_106 c
  · exact covered_0_107 c
  · exact covered_0_108 c
  · exact covered_0_109 c
  · exact covered_0_110 c
  · exact covered_0_111 c
  · exact covered_0_112 c
  · exact covered_0_113 c
  · exact covered_0_114 c
  · exact covered_0_115 c
  · exact covered_0_116 c
  · exact covered_0_117 c
  · exact covered_0_118 c
  · exact covered_0_119 c
  · exact covered_0_120 c
  · exact covered_0_121 c
  · exact covered_0_122 c
  · exact covered_0_123 c
  · exact covered_0_124 c
  · exact covered_0_125 c
  · exact covered_0_126 c
  · exact covered_0_127 c
  · exact covered_0_128 c
  · exact covered_0_129 c
  · exact covered_0_130 c
  · exact covered_0_131 c
  · exact covered_0_132 c
  · exact covered_0_133 c
  · exact covered_0_134 c
  · exact covered_0_135 c
  · exact covered_0_136 c
  · exact covered_0_137 c
  · exact covered_0_138 c
  · exact covered_0_139 c
  · exact covered_0_140 c
  · exact covered_0_141 c
  · exact covered_0_142 c
  · exact covered_0_143 c
  · exact covered_0_144 c
  · exact covered_0_145 c
  · exact covered_0_146 c
  · exact covered_0_147 c
  · exact covered_0_148 c
  · exact covered_0_149 c
  · exact covered_0_150 c
  · exact covered_0_151 c
  · exact covered_0_152 c
  · exact covered_0_153 c
  · exact covered_0_154 c
  · exact covered_0_155 c
  · exact covered_0_156 c
  · exact covered_0_157 c
  · exact covered_0_158 c
  · exact covered_0_159 c
  · exact covered_0_160 c
  · exact covered_0_161 c
  · exact covered_0_162 c
  · exact covered_0_163 c
  · exact covered_0_164 c
  · exact covered_0_165 c
  · exact covered_0_166 c
  · exact covered_0_167 c
  · exact covered_0_168 c
  · exact covered_0_169 c
  · exact covered_0_170 c
  · exact covered_0_171 c
  · exact covered_0_172 c
  · exact covered_0_173 c
  · exact covered_0_174 c
  · exact covered_0_175 c
  · exact covered_0_176 c
  · exact covered_0_177 c
  · exact covered_0_178 c
  · exact covered_0_179 c
  · exact covered_0_180 c
  · exact covered_0_181 c
  · exact covered_0_182 c
  · exact covered_0_183 c
  · exact covered_0_184 c
  · exact covered_0_185 c
  · exact covered_0_186 c
  · exact covered_0_187 c
  · exact covered_0_188 c
  · exact covered_0_189 c
  · exact covered_0_190 c
  · exact covered_0_191 c
  · exact covered_0_192 c
  · exact covered_0_193 c
  · exact covered_0_194 c
  · exact covered_0_195 c
  · exact covered_0_196 c
  · exact covered_0_197 c
  · exact covered_0_198 c
  · exact covered_0_199 c
  · exact covered_0_200 c
  · exact covered_0_201 c
  · exact covered_0_202 c
  · exact covered_0_203 c
  · exact covered_0_204 c
  · exact covered_0_205 c
  · exact covered_0_206 c
  · exact covered_0_207 c
  · exact covered_0_208 c
  · exact covered_0_209 c
  · exact covered_0_210 c
  · exact covered_0_211 c
  · exact covered_0_212 c
  · exact covered_0_213 c
  · exact covered_0_214 c
  · exact covered_0_215 c
  · exact covered_0_216 c
  · exact covered_0_217 c
  · exact covered_0_218 c
  · exact covered_0_219 c
  · exact covered_0_220 c
  · exact covered_0_221 c
  · exact covered_0_222 c
  · exact covered_0_223 c
  · exact covered_0_224 c
  · exact covered_0_225 c
  · exact covered_0_226 c
  · exact covered_0_227 c
  · exact covered_0_228 c
  · exact covered_0_229 c
  · exact covered_0_230 c
  · exact covered_0_231 c
  · exact covered_0_232 c
  · exact covered_0_233 c
  · exact covered_0_234 c
  · exact covered_0_235 c
  · exact covered_0_236 c
  · exact covered_0_237 c
  · exact covered_0_238 c
  · exact covered_0_239 c
  · exact covered_0_240 c
  · exact covered_0_241 c
  · exact covered_0_242 c
  · exact covered_0_243 c
  · exact covered_0_244 c
  · exact covered_0_245 c
  · exact covered_0_246 c
  · exact covered_0_247 c
  · exact covered_0_248 c
  · exact covered_0_249 c
  · exact covered_0_250 c
  · exact covered_0_251 c
  · exact covered_0_252 c
  · exact covered_0_253 c
  · exact covered_0_254 c
  · exact covered_0_255 c
  · exact covered_0_256 c
  · exact covered_0_257 c
  · exact covered_0_258 c
  · exact covered_0_259 c
  · exact covered_0_260 c
  · exact covered_0_261 c
  · exact covered_0_262 c
  · exact covered_0_263 c
  · exact covered_0_264 c
  · exact covered_0_265 c
  · exact covered_0_266 c
  · exact covered_0_267 c
  · exact covered_0_268 c
  · exact covered_0_269 c
  · exact covered_0_270 c
  · exact covered_0_271 c
  · exact covered_0_272 c
  · exact covered_0_273 c
  · exact covered_0_274 c
  · exact covered_0_275 c
  · exact covered_0_276 c
  · exact covered_0_277 c
  · exact covered_0_278 c
  · exact covered_0_279 c
  · exact covered_0_280 c
  · exact covered_0_281 c
  · exact covered_0_282 c
  · exact covered_0_283 c
  · exact covered_0_284 c
  · exact covered_0_285 c
  · exact covered_0_286 c
  · exact covered_0_287 c
  · exact covered_0_288 c
  · exact covered_0_289 c
  · exact covered_0_290 c
  · exact covered_0_291 c
  · exact covered_0_292 c
  · exact covered_0_293 c
  · exact covered_0_294 c
  · exact covered_0_295 c
  · exact covered_0_296 c
  · exact covered_0_297 c
  · exact covered_0_298 c
  · exact covered_0_299 c
  · exact covered_0_300 c
  · exact covered_0_301 c
  · exact covered_0_302 c
  · exact covered_0_303 c
  · exact covered_0_304 c
  · exact covered_0_305 c
  · exact covered_0_306 c
end Holant.Certificates.AffineEndpoint.BaseCertificate
