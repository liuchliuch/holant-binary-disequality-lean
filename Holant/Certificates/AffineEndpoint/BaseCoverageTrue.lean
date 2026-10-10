import Holant.Certificates.AffineEndpoint.BasePackets.Block001
import Holant.Certificates.AffineEndpoint.BasePackets.Block002
import Holant.Certificates.AffineEndpoint.BasePackets.Block003
import Holant.Certificates.AffineEndpoint.BasePackets.Block050
import Holant.Certificates.AffineEndpoint.BasePackets.Block051
import Holant.Certificates.AffineEndpoint.BasePackets.Block052
import Holant.Certificates.AffineEndpoint.BasePackets.Block053
import Holant.Certificates.AffineEndpoint.BasePackets.Block054
import Holant.Certificates.AffineEndpoint.BasePackets.Block055
import Holant.Certificates.AffineEndpoint.BasePackets.Block056
import Holant.Certificates.AffineEndpoint.BasePackets.Block057
import Holant.Certificates.AffineEndpoint.BasePackets.Block058
import Holant.Certificates.AffineEndpoint.BasePackets.Block059
import Holant.Certificates.AffineEndpoint.BasePackets.Block060
import Holant.Certificates.AffineEndpoint.BasePackets.Block061
import Holant.Certificates.AffineEndpoint.BasePackets.Block062
import Holant.Certificates.AffineEndpoint.BasePackets.Block063
import Holant.Certificates.AffineEndpoint.BasePackets.Block064
import Holant.Certificates.AffineEndpoint.BasePackets.Block065
import Holant.Certificates.AffineEndpoint.BasePackets.Block066
import Holant.Certificates.AffineEndpoint.BasePackets.Block067
import Holant.Certificates.AffineEndpoint.BasePackets.Block068
import Holant.Certificates.AffineEndpoint.BasePackets.Block069
import Holant.Certificates.AffineEndpoint.BasePackets.Block070
import Holant.Certificates.AffineEndpoint.BasePackets.Block071
import Holant.Certificates.AffineEndpoint.BasePackets.Block072
import Holant.Certificates.AffineEndpoint.BasePackets.Block073
import Holant.Certificates.AffineEndpoint.BasePackets.Block074
import Holant.Certificates.AffineEndpoint.BasePackets.Block075
import Holant.Certificates.AffineEndpoint.BasePackets.Block076
import Holant.Certificates.AffineEndpoint.BasePackets.Block077
import Holant.Certificates.AffineEndpoint.BasePackets.Block078
import Holant.Certificates.AffineEndpoint.BasePackets.Block079
import Holant.Certificates.AffineEndpoint.BasePackets.Block080
import Holant.Certificates.AffineEndpoint.BasePackets.Block081
import Holant.Certificates.AffineEndpoint.BasePackets.Block082
import Holant.Certificates.AffineEndpoint.BasePackets.Block083
import Holant.Certificates.AffineEndpoint.BasePackets.Block084
import Holant.Certificates.AffineEndpoint.BasePackets.Block085
import Holant.Certificates.AffineEndpoint.BasePackets.Block086
import Holant.Certificates.AffineEndpoint.BasePackets.Block087
import Holant.Certificates.AffineEndpoint.BasePackets.Block088
import Holant.Certificates.AffineEndpoint.BasePackets.Block089
import Holant.Certificates.AffineEndpoint.BasePackets.Block090
import Holant.Certificates.AffineEndpoint.BasePackets.Block091
import Holant.Certificates.AffineEndpoint.BasePackets.Block092
import Holant.Certificates.AffineEndpoint.BasePackets.Block093
import Holant.Certificates.AffineEndpoint.BasePackets.Block094
import Holant.Certificates.AffineEndpoint.BasePackets.Block095
import Holant.Certificates.AffineEndpoint.BasePackets.Block096
import Holant.Certificates.AffineEndpoint.PacketCoverage
import Holant.Certificates.AffineEndpoint.BaseTransform
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
open SupportCatalog
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false
 theorem covered_1_000 (c : Fin 1) : ∃w,BaseWitnessCheck 0 c.val true w := by
  refine ⟨packetData0807.getD c.val 0,?_⟩
  have h := packetCheck_sound 0 true 0 packetData0807 packetPass0807 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_001 (c : Fin 1) : ∃w,BaseWitnessCheck 1 c.val true w := by
  refine ⟨packetData0808.getD c.val 0,?_⟩
  have h := packetCheck_sound 1 true 0 packetData0808 packetPass0808 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_002 (c : Fin 1) : ∃w,BaseWitnessCheck 2 c.val true w := by
  refine ⟨packetData0809.getD c.val 0,?_⟩
  have h := packetCheck_sound 2 true 0 packetData0809 packetPass0809 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_003 (c : Fin 1) : ∃w,BaseWitnessCheck 3 c.val true w := by
  refine ⟨packetData0810.getD c.val 0,?_⟩
  have h := packetCheck_sound 3 true 0 packetData0810 packetPass0810 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_004 (c : Fin 1) : ∃w,BaseWitnessCheck 4 c.val true w := by
  refine ⟨packetData0811.getD c.val 0,?_⟩
  have h := packetCheck_sound 4 true 0 packetData0811 packetPass0811 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_005 (c : Fin 1) : ∃w,BaseWitnessCheck 5 c.val true w := by
  refine ⟨packetData0812.getD c.val 0,?_⟩
  have h := packetCheck_sound 5 true 0 packetData0812 packetPass0812 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_006 (c : Fin 1) : ∃w,BaseWitnessCheck 6 c.val true w := by
  refine ⟨packetData0813.getD c.val 0,?_⟩
  have h := packetCheck_sound 6 true 0 packetData0813 packetPass0813 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_007 (c : Fin 1) : ∃w,BaseWitnessCheck 7 c.val true w := by
  refine ⟨packetData0814.getD c.val 0,?_⟩
  have h := packetCheck_sound 7 true 0 packetData0814 packetPass0814 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_008 (c : Fin 1) : ∃w,BaseWitnessCheck 8 c.val true w := by
  refine ⟨packetData0815.getD c.val 0,?_⟩
  have h := packetCheck_sound 8 true 0 packetData0815 packetPass0815 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_009 (c : Fin 1) : ∃w,BaseWitnessCheck 9 c.val true w := by
  refine ⟨packetData0816.getD c.val 0,?_⟩
  have h := packetCheck_sound 9 true 0 packetData0816 packetPass0816 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_010 (c : Fin 1) : ∃w,BaseWitnessCheck 10 c.val true w := by
  refine ⟨packetData0817.getD c.val 0,?_⟩
  have h := packetCheck_sound 10 true 0 packetData0817 packetPass0817 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_011 (c : Fin 1) : ∃w,BaseWitnessCheck 11 c.val true w := by
  refine ⟨packetData0818.getD c.val 0,?_⟩
  have h := packetCheck_sound 11 true 0 packetData0818 packetPass0818 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_012 (c : Fin 1) : ∃w,BaseWitnessCheck 12 c.val true w := by
  refine ⟨packetData0819.getD c.val 0,?_⟩
  have h := packetCheck_sound 12 true 0 packetData0819 packetPass0819 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_013 (c : Fin 1) : ∃w,BaseWitnessCheck 13 c.val true w := by
  refine ⟨packetData0820.getD c.val 0,?_⟩
  have h := packetCheck_sound 13 true 0 packetData0820 packetPass0820 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_014 (c : Fin 1) : ∃w,BaseWitnessCheck 14 c.val true w := by
  refine ⟨packetData0821.getD c.val 0,?_⟩
  have h := packetCheck_sound 14 true 0 packetData0821 packetPass0821 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_015 (c : Fin 1) : ∃w,BaseWitnessCheck 15 c.val true w := by
  refine ⟨packetData0822.getD c.val 0,?_⟩
  have h := packetCheck_sound 15 true 0 packetData0822 packetPass0822 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_016 (c : Fin 4) : ∃w,BaseWitnessCheck 16 c.val true w := by
  refine ⟨packetData0823.getD c.val 0,?_⟩
  have h := packetCheck_sound 16 true 0 packetData0823 packetPass0823 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_017 (c : Fin 4) : ∃w,BaseWitnessCheck 17 c.val true w := by
  refine ⟨packetData0824.getD c.val 0,?_⟩
  have h := packetCheck_sound 17 true 0 packetData0824 packetPass0824 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_018 (c : Fin 4) : ∃w,BaseWitnessCheck 18 c.val true w := by
  refine ⟨packetData0825.getD c.val 0,?_⟩
  have h := packetCheck_sound 18 true 0 packetData0825 packetPass0825 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_019 (c : Fin 4) : ∃w,BaseWitnessCheck 19 c.val true w := by
  refine ⟨packetData0826.getD c.val 0,?_⟩
  have h := packetCheck_sound 19 true 0 packetData0826 packetPass0826 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_020 (c : Fin 4) : ∃w,BaseWitnessCheck 20 c.val true w := by
  refine ⟨packetData0827.getD c.val 0,?_⟩
  have h := packetCheck_sound 20 true 0 packetData0827 packetPass0827 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_021 (c : Fin 4) : ∃w,BaseWitnessCheck 21 c.val true w := by
  refine ⟨packetData0828.getD c.val 0,?_⟩
  have h := packetCheck_sound 21 true 0 packetData0828 packetPass0828 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_022 (c : Fin 4) : ∃w,BaseWitnessCheck 22 c.val true w := by
  refine ⟨packetData0829.getD c.val 0,?_⟩
  have h := packetCheck_sound 22 true 0 packetData0829 packetPass0829 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_023 (c : Fin 4) : ∃w,BaseWitnessCheck 23 c.val true w := by
  refine ⟨packetData0830.getD c.val 0,?_⟩
  have h := packetCheck_sound 23 true 0 packetData0830 packetPass0830 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_024 (c : Fin 4) : ∃w,BaseWitnessCheck 24 c.val true w := by
  refine ⟨packetData0831.getD c.val 0,?_⟩
  have h := packetCheck_sound 24 true 0 packetData0831 packetPass0831 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_025 (c : Fin 4) : ∃w,BaseWitnessCheck 25 c.val true w := by
  refine ⟨packetData0832.getD c.val 0,?_⟩
  have h := packetCheck_sound 25 true 0 packetData0832 packetPass0832 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_026 (c : Fin 4) : ∃w,BaseWitnessCheck 26 c.val true w := by
  refine ⟨packetData0833.getD c.val 0,?_⟩
  have h := packetCheck_sound 26 true 0 packetData0833 packetPass0833 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_027 (c : Fin 4) : ∃w,BaseWitnessCheck 27 c.val true w := by
  refine ⟨packetData0834.getD c.val 0,?_⟩
  have h := packetCheck_sound 27 true 0 packetData0834 packetPass0834 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_028 (c : Fin 4) : ∃w,BaseWitnessCheck 28 c.val true w := by
  refine ⟨packetData0835.getD c.val 0,?_⟩
  have h := packetCheck_sound 28 true 0 packetData0835 packetPass0835 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_029 (c : Fin 4) : ∃w,BaseWitnessCheck 29 c.val true w := by
  refine ⟨packetData0836.getD c.val 0,?_⟩
  have h := packetCheck_sound 29 true 0 packetData0836 packetPass0836 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_030 (c : Fin 4) : ∃w,BaseWitnessCheck 30 c.val true w := by
  refine ⟨packetData0837.getD c.val 0,?_⟩
  have h := packetCheck_sound 30 true 0 packetData0837 packetPass0837 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_031 (c : Fin 4) : ∃w,BaseWitnessCheck 31 c.val true w := by
  refine ⟨packetData0838.getD c.val 0,?_⟩
  have h := packetCheck_sound 31 true 0 packetData0838 packetPass0838 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_032 (c : Fin 4) : ∃w,BaseWitnessCheck 32 c.val true w := by
  refine ⟨packetData0839.getD c.val 0,?_⟩
  have h := packetCheck_sound 32 true 0 packetData0839 packetPass0839 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_033 (c : Fin 4) : ∃w,BaseWitnessCheck 33 c.val true w := by
  refine ⟨packetData0840.getD c.val 0,?_⟩
  have h := packetCheck_sound 33 true 0 packetData0840 packetPass0840 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_034 (c : Fin 4) : ∃w,BaseWitnessCheck 34 c.val true w := by
  refine ⟨packetData0841.getD c.val 0,?_⟩
  have h := packetCheck_sound 34 true 0 packetData0841 packetPass0841 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_035 (c : Fin 4) : ∃w,BaseWitnessCheck 35 c.val true w := by
  refine ⟨packetData0842.getD c.val 0,?_⟩
  have h := packetCheck_sound 35 true 0 packetData0842 packetPass0842 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_036 (c : Fin 4) : ∃w,BaseWitnessCheck 36 c.val true w := by
  refine ⟨packetData0843.getD c.val 0,?_⟩
  have h := packetCheck_sound 36 true 0 packetData0843 packetPass0843 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_037 (c : Fin 4) : ∃w,BaseWitnessCheck 37 c.val true w := by
  refine ⟨packetData0844.getD c.val 0,?_⟩
  have h := packetCheck_sound 37 true 0 packetData0844 packetPass0844 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_038 (c : Fin 4) : ∃w,BaseWitnessCheck 38 c.val true w := by
  refine ⟨packetData0845.getD c.val 0,?_⟩
  have h := packetCheck_sound 38 true 0 packetData0845 packetPass0845 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_039 (c : Fin 4) : ∃w,BaseWitnessCheck 39 c.val true w := by
  refine ⟨packetData0846.getD c.val 0,?_⟩
  have h := packetCheck_sound 39 true 0 packetData0846 packetPass0846 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_040 (c : Fin 4) : ∃w,BaseWitnessCheck 40 c.val true w := by
  refine ⟨packetData0847.getD c.val 0,?_⟩
  have h := packetCheck_sound 40 true 0 packetData0847 packetPass0847 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_041 (c : Fin 4) : ∃w,BaseWitnessCheck 41 c.val true w := by
  refine ⟨packetData0848.getD c.val 0,?_⟩
  have h := packetCheck_sound 41 true 0 packetData0848 packetPass0848 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_042 (c : Fin 4) : ∃w,BaseWitnessCheck 42 c.val true w := by
  refine ⟨packetData0849.getD c.val 0,?_⟩
  have h := packetCheck_sound 42 true 0 packetData0849 packetPass0849 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_043 (c : Fin 4) : ∃w,BaseWitnessCheck 43 c.val true w := by
  refine ⟨packetData0850.getD c.val 0,?_⟩
  have h := packetCheck_sound 43 true 0 packetData0850 packetPass0850 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_044 (c : Fin 4) : ∃w,BaseWitnessCheck 44 c.val true w := by
  refine ⟨packetData0851.getD c.val 0,?_⟩
  have h := packetCheck_sound 44 true 0 packetData0851 packetPass0851 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_045 (c : Fin 4) : ∃w,BaseWitnessCheck 45 c.val true w := by
  refine ⟨packetData0852.getD c.val 0,?_⟩
  have h := packetCheck_sound 45 true 0 packetData0852 packetPass0852 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_046 (c : Fin 4) : ∃w,BaseWitnessCheck 46 c.val true w := by
  refine ⟨packetData0853.getD c.val 0,?_⟩
  have h := packetCheck_sound 46 true 0 packetData0853 packetPass0853 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_047 (c : Fin 4) : ∃w,BaseWitnessCheck 47 c.val true w := by
  refine ⟨packetData0854.getD c.val 0,?_⟩
  have h := packetCheck_sound 47 true 0 packetData0854 packetPass0854 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_048 (c : Fin 4) : ∃w,BaseWitnessCheck 48 c.val true w := by
  refine ⟨packetData0855.getD c.val 0,?_⟩
  have h := packetCheck_sound 48 true 0 packetData0855 packetPass0855 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_049 (c : Fin 4) : ∃w,BaseWitnessCheck 49 c.val true w := by
  refine ⟨packetData0856.getD c.val 0,?_⟩
  have h := packetCheck_sound 49 true 0 packetData0856 packetPass0856 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_050 (c : Fin 4) : ∃w,BaseWitnessCheck 50 c.val true w := by
  refine ⟨packetData0857.getD c.val 0,?_⟩
  have h := packetCheck_sound 50 true 0 packetData0857 packetPass0857 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_051 (c : Fin 4) : ∃w,BaseWitnessCheck 51 c.val true w := by
  refine ⟨packetData0858.getD c.val 0,?_⟩
  have h := packetCheck_sound 51 true 0 packetData0858 packetPass0858 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_052 (c : Fin 4) : ∃w,BaseWitnessCheck 52 c.val true w := by
  refine ⟨packetData0859.getD c.val 0,?_⟩
  have h := packetCheck_sound 52 true 0 packetData0859 packetPass0859 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_053 (c : Fin 4) : ∃w,BaseWitnessCheck 53 c.val true w := by
  refine ⟨packetData0860.getD c.val 0,?_⟩
  have h := packetCheck_sound 53 true 0 packetData0860 packetPass0860 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_054 (c : Fin 4) : ∃w,BaseWitnessCheck 54 c.val true w := by
  refine ⟨packetData0861.getD c.val 0,?_⟩
  have h := packetCheck_sound 54 true 0 packetData0861 packetPass0861 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_055 (c : Fin 4) : ∃w,BaseWitnessCheck 55 c.val true w := by
  refine ⟨packetData0862.getD c.val 0,?_⟩
  have h := packetCheck_sound 55 true 0 packetData0862 packetPass0862 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_056 (c : Fin 4) : ∃w,BaseWitnessCheck 56 c.val true w := by
  refine ⟨packetData0863.getD c.val 0,?_⟩
  have h := packetCheck_sound 56 true 0 packetData0863 packetPass0863 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_057 (c : Fin 4) : ∃w,BaseWitnessCheck 57 c.val true w := by
  refine ⟨packetData0864.getD c.val 0,?_⟩
  have h := packetCheck_sound 57 true 0 packetData0864 packetPass0864 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_058 (c : Fin 4) : ∃w,BaseWitnessCheck 58 c.val true w := by
  refine ⟨packetData0865.getD c.val 0,?_⟩
  have h := packetCheck_sound 58 true 0 packetData0865 packetPass0865 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_059 (c : Fin 4) : ∃w,BaseWitnessCheck 59 c.val true w := by
  refine ⟨packetData0866.getD c.val 0,?_⟩
  have h := packetCheck_sound 59 true 0 packetData0866 packetPass0866 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_060 (c : Fin 4) : ∃w,BaseWitnessCheck 60 c.val true w := by
  refine ⟨packetData0867.getD c.val 0,?_⟩
  have h := packetCheck_sound 60 true 0 packetData0867 packetPass0867 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_061 (c : Fin 4) : ∃w,BaseWitnessCheck 61 c.val true w := by
  refine ⟨packetData0868.getD c.val 0,?_⟩
  have h := packetCheck_sound 61 true 0 packetData0868 packetPass0868 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_062 (c : Fin 4) : ∃w,BaseWitnessCheck 62 c.val true w := by
  refine ⟨packetData0869.getD c.val 0,?_⟩
  have h := packetCheck_sound 62 true 0 packetData0869 packetPass0869 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_063 (c : Fin 4) : ∃w,BaseWitnessCheck 63 c.val true w := by
  refine ⟨packetData0870.getD c.val 0,?_⟩
  have h := packetCheck_sound 63 true 0 packetData0870 packetPass0870 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_064 (c : Fin 4) : ∃w,BaseWitnessCheck 64 c.val true w := by
  refine ⟨packetData0871.getD c.val 0,?_⟩
  have h := packetCheck_sound 64 true 0 packetData0871 packetPass0871 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_065 (c : Fin 4) : ∃w,BaseWitnessCheck 65 c.val true w := by
  refine ⟨packetData0872.getD c.val 0,?_⟩
  have h := packetCheck_sound 65 true 0 packetData0872 packetPass0872 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_066 (c : Fin 4) : ∃w,BaseWitnessCheck 66 c.val true w := by
  refine ⟨packetData0873.getD c.val 0,?_⟩
  have h := packetCheck_sound 66 true 0 packetData0873 packetPass0873 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_067 (c : Fin 4) : ∃w,BaseWitnessCheck 67 c.val true w := by
  refine ⟨packetData0874.getD c.val 0,?_⟩
  have h := packetCheck_sound 67 true 0 packetData0874 packetPass0874 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_068 (c : Fin 4) : ∃w,BaseWitnessCheck 68 c.val true w := by
  refine ⟨packetData0875.getD c.val 0,?_⟩
  have h := packetCheck_sound 68 true 0 packetData0875 packetPass0875 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_069 (c : Fin 4) : ∃w,BaseWitnessCheck 69 c.val true w := by
  refine ⟨packetData0876.getD c.val 0,?_⟩
  have h := packetCheck_sound 69 true 0 packetData0876 packetPass0876 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_070 (c : Fin 4) : ∃w,BaseWitnessCheck 70 c.val true w := by
  refine ⟨packetData0877.getD c.val 0,?_⟩
  have h := packetCheck_sound 70 true 0 packetData0877 packetPass0877 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_071 (c : Fin 4) : ∃w,BaseWitnessCheck 71 c.val true w := by
  refine ⟨packetData0878.getD c.val 0,?_⟩
  have h := packetCheck_sound 71 true 0 packetData0878 packetPass0878 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_072 (c : Fin 4) : ∃w,BaseWitnessCheck 72 c.val true w := by
  refine ⟨packetData0879.getD c.val 0,?_⟩
  have h := packetCheck_sound 72 true 0 packetData0879 packetPass0879 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_073 (c : Fin 4) : ∃w,BaseWitnessCheck 73 c.val true w := by
  refine ⟨packetData0880.getD c.val 0,?_⟩
  have h := packetCheck_sound 73 true 0 packetData0880 packetPass0880 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_074 (c : Fin 4) : ∃w,BaseWitnessCheck 74 c.val true w := by
  refine ⟨packetData0881.getD c.val 0,?_⟩
  have h := packetCheck_sound 74 true 0 packetData0881 packetPass0881 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_075 (c : Fin 4) : ∃w,BaseWitnessCheck 75 c.val true w := by
  refine ⟨packetData0882.getD c.val 0,?_⟩
  have h := packetCheck_sound 75 true 0 packetData0882 packetPass0882 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_076 (c : Fin 4) : ∃w,BaseWitnessCheck 76 c.val true w := by
  refine ⟨packetData0883.getD c.val 0,?_⟩
  have h := packetCheck_sound 76 true 0 packetData0883 packetPass0883 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_077 (c : Fin 4) : ∃w,BaseWitnessCheck 77 c.val true w := by
  refine ⟨packetData0884.getD c.val 0,?_⟩
  have h := packetCheck_sound 77 true 0 packetData0884 packetPass0884 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_078 (c : Fin 4) : ∃w,BaseWitnessCheck 78 c.val true w := by
  refine ⟨packetData0885.getD c.val 0,?_⟩
  have h := packetCheck_sound 78 true 0 packetData0885 packetPass0885 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_079 (c : Fin 4) : ∃w,BaseWitnessCheck 79 c.val true w := by
  refine ⟨packetData0886.getD c.val 0,?_⟩
  have h := packetCheck_sound 79 true 0 packetData0886 packetPass0886 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_080 (c : Fin 4) : ∃w,BaseWitnessCheck 80 c.val true w := by
  refine ⟨packetData0887.getD c.val 0,?_⟩
  have h := packetCheck_sound 80 true 0 packetData0887 packetPass0887 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_081 (c : Fin 4) : ∃w,BaseWitnessCheck 81 c.val true w := by
  refine ⟨packetData0888.getD c.val 0,?_⟩
  have h := packetCheck_sound 81 true 0 packetData0888 packetPass0888 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_082 (c : Fin 4) : ∃w,BaseWitnessCheck 82 c.val true w := by
  refine ⟨packetData0889.getD c.val 0,?_⟩
  have h := packetCheck_sound 82 true 0 packetData0889 packetPass0889 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_083 (c : Fin 4) : ∃w,BaseWitnessCheck 83 c.val true w := by
  refine ⟨packetData0890.getD c.val 0,?_⟩
  have h := packetCheck_sound 83 true 0 packetData0890 packetPass0890 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_084 (c : Fin 4) : ∃w,BaseWitnessCheck 84 c.val true w := by
  refine ⟨packetData0891.getD c.val 0,?_⟩
  have h := packetCheck_sound 84 true 0 packetData0891 packetPass0891 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_085 (c : Fin 4) : ∃w,BaseWitnessCheck 85 c.val true w := by
  refine ⟨packetData0892.getD c.val 0,?_⟩
  have h := packetCheck_sound 85 true 0 packetData0892 packetPass0892 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_086 (c : Fin 4) : ∃w,BaseWitnessCheck 86 c.val true w := by
  refine ⟨packetData0893.getD c.val 0,?_⟩
  have h := packetCheck_sound 86 true 0 packetData0893 packetPass0893 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_087 (c : Fin 4) : ∃w,BaseWitnessCheck 87 c.val true w := by
  refine ⟨packetData0894.getD c.val 0,?_⟩
  have h := packetCheck_sound 87 true 0 packetData0894 packetPass0894 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_088 (c : Fin 4) : ∃w,BaseWitnessCheck 88 c.val true w := by
  refine ⟨packetData0895.getD c.val 0,?_⟩
  have h := packetCheck_sound 88 true 0 packetData0895 packetPass0895 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_089 (c : Fin 4) : ∃w,BaseWitnessCheck 89 c.val true w := by
  refine ⟨packetData0896.getD c.val 0,?_⟩
  have h := packetCheck_sound 89 true 0 packetData0896 packetPass0896 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_090 (c : Fin 4) : ∃w,BaseWitnessCheck 90 c.val true w := by
  refine ⟨packetData0897.getD c.val 0,?_⟩
  have h := packetCheck_sound 90 true 0 packetData0897 packetPass0897 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_091 (c : Fin 4) : ∃w,BaseWitnessCheck 91 c.val true w := by
  refine ⟨packetData0898.getD c.val 0,?_⟩
  have h := packetCheck_sound 91 true 0 packetData0898 packetPass0898 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_092 (c : Fin 4) : ∃w,BaseWitnessCheck 92 c.val true w := by
  refine ⟨packetData0899.getD c.val 0,?_⟩
  have h := packetCheck_sound 92 true 0 packetData0899 packetPass0899 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_093 (c : Fin 4) : ∃w,BaseWitnessCheck 93 c.val true w := by
  refine ⟨packetData0900.getD c.val 0,?_⟩
  have h := packetCheck_sound 93 true 0 packetData0900 packetPass0900 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_094 (c : Fin 4) : ∃w,BaseWitnessCheck 94 c.val true w := by
  refine ⟨packetData0901.getD c.val 0,?_⟩
  have h := packetCheck_sound 94 true 0 packetData0901 packetPass0901 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_095 (c : Fin 4) : ∃w,BaseWitnessCheck 95 c.val true w := by
  refine ⟨packetData0902.getD c.val 0,?_⟩
  have h := packetCheck_sound 95 true 0 packetData0902 packetPass0902 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_096 (c : Fin 4) : ∃w,BaseWitnessCheck 96 c.val true w := by
  refine ⟨packetData0903.getD c.val 0,?_⟩
  have h := packetCheck_sound 96 true 0 packetData0903 packetPass0903 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_097 (c : Fin 4) : ∃w,BaseWitnessCheck 97 c.val true w := by
  refine ⟨packetData0904.getD c.val 0,?_⟩
  have h := packetCheck_sound 97 true 0 packetData0904 packetPass0904 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_098 (c : Fin 4) : ∃w,BaseWitnessCheck 98 c.val true w := by
  refine ⟨packetData0905.getD c.val 0,?_⟩
  have h := packetCheck_sound 98 true 0 packetData0905 packetPass0905 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_099 (c : Fin 4) : ∃w,BaseWitnessCheck 99 c.val true w := by
  refine ⟨packetData0906.getD c.val 0,?_⟩
  have h := packetCheck_sound 99 true 0 packetData0906 packetPass0906 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_100 (c : Fin 4) : ∃w,BaseWitnessCheck 100 c.val true w := by
  refine ⟨packetData0907.getD c.val 0,?_⟩
  have h := packetCheck_sound 100 true 0 packetData0907 packetPass0907 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_101 (c : Fin 4) : ∃w,BaseWitnessCheck 101 c.val true w := by
  refine ⟨packetData0908.getD c.val 0,?_⟩
  have h := packetCheck_sound 101 true 0 packetData0908 packetPass0908 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_102 (c : Fin 4) : ∃w,BaseWitnessCheck 102 c.val true w := by
  refine ⟨packetData0909.getD c.val 0,?_⟩
  have h := packetCheck_sound 102 true 0 packetData0909 packetPass0909 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_103 (c : Fin 4) : ∃w,BaseWitnessCheck 103 c.val true w := by
  refine ⟨packetData0910.getD c.val 0,?_⟩
  have h := packetCheck_sound 103 true 0 packetData0910 packetPass0910 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_104 (c : Fin 4) : ∃w,BaseWitnessCheck 104 c.val true w := by
  refine ⟨packetData0911.getD c.val 0,?_⟩
  have h := packetCheck_sound 104 true 0 packetData0911 packetPass0911 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_105 (c : Fin 4) : ∃w,BaseWitnessCheck 105 c.val true w := by
  refine ⟨packetData0912.getD c.val 0,?_⟩
  have h := packetCheck_sound 105 true 0 packetData0912 packetPass0912 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_106 (c : Fin 4) : ∃w,BaseWitnessCheck 106 c.val true w := by
  refine ⟨packetData0913.getD c.val 0,?_⟩
  have h := packetCheck_sound 106 true 0 packetData0913 packetPass0913 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_107 (c : Fin 4) : ∃w,BaseWitnessCheck 107 c.val true w := by
  refine ⟨packetData0914.getD c.val 0,?_⟩
  have h := packetCheck_sound 107 true 0 packetData0914 packetPass0914 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_108 (c : Fin 4) : ∃w,BaseWitnessCheck 108 c.val true w := by
  refine ⟨packetData0915.getD c.val 0,?_⟩
  have h := packetCheck_sound 108 true 0 packetData0915 packetPass0915 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_109 (c : Fin 4) : ∃w,BaseWitnessCheck 109 c.val true w := by
  refine ⟨packetData0916.getD c.val 0,?_⟩
  have h := packetCheck_sound 109 true 0 packetData0916 packetPass0916 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_110 (c : Fin 4) : ∃w,BaseWitnessCheck 110 c.val true w := by
  refine ⟨packetData0917.getD c.val 0,?_⟩
  have h := packetCheck_sound 110 true 0 packetData0917 packetPass0917 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_111 (c : Fin 4) : ∃w,BaseWitnessCheck 111 c.val true w := by
  refine ⟨packetData0918.getD c.val 0,?_⟩
  have h := packetCheck_sound 111 true 0 packetData0918 packetPass0918 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_112 (c : Fin 4) : ∃w,BaseWitnessCheck 112 c.val true w := by
  refine ⟨packetData0919.getD c.val 0,?_⟩
  have h := packetCheck_sound 112 true 0 packetData0919 packetPass0919 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_113 (c : Fin 4) : ∃w,BaseWitnessCheck 113 c.val true w := by
  refine ⟨packetData0920.getD c.val 0,?_⟩
  have h := packetCheck_sound 113 true 0 packetData0920 packetPass0920 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_114 (c : Fin 4) : ∃w,BaseWitnessCheck 114 c.val true w := by
  refine ⟨packetData0921.getD c.val 0,?_⟩
  have h := packetCheck_sound 114 true 0 packetData0921 packetPass0921 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_115 (c : Fin 4) : ∃w,BaseWitnessCheck 115 c.val true w := by
  refine ⟨packetData0922.getD c.val 0,?_⟩
  have h := packetCheck_sound 115 true 0 packetData0922 packetPass0922 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_116 (c : Fin 4) : ∃w,BaseWitnessCheck 116 c.val true w := by
  refine ⟨packetData0923.getD c.val 0,?_⟩
  have h := packetCheck_sound 116 true 0 packetData0923 packetPass0923 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_117 (c : Fin 4) : ∃w,BaseWitnessCheck 117 c.val true w := by
  refine ⟨packetData0924.getD c.val 0,?_⟩
  have h := packetCheck_sound 117 true 0 packetData0924 packetPass0924 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_118 (c : Fin 4) : ∃w,BaseWitnessCheck 118 c.val true w := by
  refine ⟨packetData0925.getD c.val 0,?_⟩
  have h := packetCheck_sound 118 true 0 packetData0925 packetPass0925 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_119 (c : Fin 4) : ∃w,BaseWitnessCheck 119 c.val true w := by
  refine ⟨packetData0926.getD c.val 0,?_⟩
  have h := packetCheck_sound 119 true 0 packetData0926 packetPass0926 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_120 (c : Fin 4) : ∃w,BaseWitnessCheck 120 c.val true w := by
  refine ⟨packetData0927.getD c.val 0,?_⟩
  have h := packetCheck_sound 120 true 0 packetData0927 packetPass0927 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_121 (c : Fin 4) : ∃w,BaseWitnessCheck 121 c.val true w := by
  refine ⟨packetData0928.getD c.val 0,?_⟩
  have h := packetCheck_sound 121 true 0 packetData0928 packetPass0928 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_122 (c : Fin 4) : ∃w,BaseWitnessCheck 122 c.val true w := by
  refine ⟨packetData0929.getD c.val 0,?_⟩
  have h := packetCheck_sound 122 true 0 packetData0929 packetPass0929 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_123 (c : Fin 4) : ∃w,BaseWitnessCheck 123 c.val true w := by
  refine ⟨packetData0930.getD c.val 0,?_⟩
  have h := packetCheck_sound 123 true 0 packetData0930 packetPass0930 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_124 (c : Fin 4) : ∃w,BaseWitnessCheck 124 c.val true w := by
  refine ⟨packetData0931.getD c.val 0,?_⟩
  have h := packetCheck_sound 124 true 0 packetData0931 packetPass0931 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_125 (c : Fin 4) : ∃w,BaseWitnessCheck 125 c.val true w := by
  refine ⟨packetData0932.getD c.val 0,?_⟩
  have h := packetCheck_sound 125 true 0 packetData0932 packetPass0932 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_126 (c : Fin 4) : ∃w,BaseWitnessCheck 126 c.val true w := by
  refine ⟨packetData0933.getD c.val 0,?_⟩
  have h := packetCheck_sound 126 true 0 packetData0933 packetPass0933 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_127 (c : Fin 4) : ∃w,BaseWitnessCheck 127 c.val true w := by
  refine ⟨packetData0934.getD c.val 0,?_⟩
  have h := packetCheck_sound 127 true 0 packetData0934 packetPass0934 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_128 (c : Fin 4) : ∃w,BaseWitnessCheck 128 c.val true w := by
  refine ⟨packetData0935.getD c.val 0,?_⟩
  have h := packetCheck_sound 128 true 0 packetData0935 packetPass0935 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_129 (c : Fin 4) : ∃w,BaseWitnessCheck 129 c.val true w := by
  refine ⟨packetData0936.getD c.val 0,?_⟩
  have h := packetCheck_sound 129 true 0 packetData0936 packetPass0936 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_130 (c : Fin 4) : ∃w,BaseWitnessCheck 130 c.val true w := by
  refine ⟨packetData0937.getD c.val 0,?_⟩
  have h := packetCheck_sound 130 true 0 packetData0937 packetPass0937 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_131 (c : Fin 4) : ∃w,BaseWitnessCheck 131 c.val true w := by
  refine ⟨packetData0938.getD c.val 0,?_⟩
  have h := packetCheck_sound 131 true 0 packetData0938 packetPass0938 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_132 (c : Fin 4) : ∃w,BaseWitnessCheck 132 c.val true w := by
  refine ⟨packetData0939.getD c.val 0,?_⟩
  have h := packetCheck_sound 132 true 0 packetData0939 packetPass0939 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_133 (c : Fin 4) : ∃w,BaseWitnessCheck 133 c.val true w := by
  refine ⟨packetData0940.getD c.val 0,?_⟩
  have h := packetCheck_sound 133 true 0 packetData0940 packetPass0940 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_134 (c : Fin 4) : ∃w,BaseWitnessCheck 134 c.val true w := by
  refine ⟨packetData0941.getD c.val 0,?_⟩
  have h := packetCheck_sound 134 true 0 packetData0941 packetPass0941 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_135 (c : Fin 4) : ∃w,BaseWitnessCheck 135 c.val true w := by
  refine ⟨packetData0942.getD c.val 0,?_⟩
  have h := packetCheck_sound 135 true 0 packetData0942 packetPass0942 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_136 (c : Fin 32) : ∃w,BaseWitnessCheck 136 c.val true w := by
  refine ⟨packetData0943.getD c.val 0,?_⟩
  have h := packetCheck_sound 136 true 0 packetData0943 packetPass0943 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_137 (c : Fin 32) : ∃w,BaseWitnessCheck 137 c.val true w := by
  refine ⟨packetData0944.getD c.val 0,?_⟩
  have h := packetCheck_sound 137 true 0 packetData0944 packetPass0944 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_138 (c : Fin 32) : ∃w,BaseWitnessCheck 138 c.val true w := by
  refine ⟨packetData0945.getD c.val 0,?_⟩
  have h := packetCheck_sound 138 true 0 packetData0945 packetPass0945 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_139 (c : Fin 32) : ∃w,BaseWitnessCheck 139 c.val true w := by
  refine ⟨packetData0946.getD c.val 0,?_⟩
  have h := packetCheck_sound 139 true 0 packetData0946 packetPass0946 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_140 (c : Fin 32) : ∃w,BaseWitnessCheck 140 c.val true w := by
  refine ⟨packetData0947.getD c.val 0,?_⟩
  have h := packetCheck_sound 140 true 0 packetData0947 packetPass0947 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_141 (c : Fin 32) : ∃w,BaseWitnessCheck 141 c.val true w := by
  refine ⟨packetData0948.getD c.val 0,?_⟩
  have h := packetCheck_sound 141 true 0 packetData0948 packetPass0948 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_142 (c : Fin 32) : ∃w,BaseWitnessCheck 142 c.val true w := by
  refine ⟨packetData0949.getD c.val 0,?_⟩
  have h := packetCheck_sound 142 true 0 packetData0949 packetPass0949 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_143 (c : Fin 32) : ∃w,BaseWitnessCheck 143 c.val true w := by
  refine ⟨packetData0950.getD c.val 0,?_⟩
  have h := packetCheck_sound 143 true 0 packetData0950 packetPass0950 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_144 (c : Fin 32) : ∃w,BaseWitnessCheck 144 c.val true w := by
  refine ⟨packetData0951.getD c.val 0,?_⟩
  have h := packetCheck_sound 144 true 0 packetData0951 packetPass0951 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_145 (c : Fin 32) : ∃w,BaseWitnessCheck 145 c.val true w := by
  refine ⟨packetData0952.getD c.val 0,?_⟩
  have h := packetCheck_sound 145 true 0 packetData0952 packetPass0952 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_146 (c : Fin 32) : ∃w,BaseWitnessCheck 146 c.val true w := by
  refine ⟨packetData0953.getD c.val 0,?_⟩
  have h := packetCheck_sound 146 true 0 packetData0953 packetPass0953 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_147 (c : Fin 32) : ∃w,BaseWitnessCheck 147 c.val true w := by
  refine ⟨packetData0954.getD c.val 0,?_⟩
  have h := packetCheck_sound 147 true 0 packetData0954 packetPass0954 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_148 (c : Fin 32) : ∃w,BaseWitnessCheck 148 c.val true w := by
  refine ⟨packetData0955.getD c.val 0,?_⟩
  have h := packetCheck_sound 148 true 0 packetData0955 packetPass0955 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_149 (c : Fin 32) : ∃w,BaseWitnessCheck 149 c.val true w := by
  refine ⟨packetData0956.getD c.val 0,?_⟩
  have h := packetCheck_sound 149 true 0 packetData0956 packetPass0956 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_150 (c : Fin 32) : ∃w,BaseWitnessCheck 150 c.val true w := by
  refine ⟨packetData0957.getD c.val 0,?_⟩
  have h := packetCheck_sound 150 true 0 packetData0957 packetPass0957 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_151 (c : Fin 32) : ∃w,BaseWitnessCheck 151 c.val true w := by
  refine ⟨packetData0958.getD c.val 0,?_⟩
  have h := packetCheck_sound 151 true 0 packetData0958 packetPass0958 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_152 (c : Fin 32) : ∃w,BaseWitnessCheck 152 c.val true w := by
  refine ⟨packetData0959.getD c.val 0,?_⟩
  have h := packetCheck_sound 152 true 0 packetData0959 packetPass0959 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_153 (c : Fin 32) : ∃w,BaseWitnessCheck 153 c.val true w := by
  refine ⟨packetData0960.getD c.val 0,?_⟩
  have h := packetCheck_sound 153 true 0 packetData0960 packetPass0960 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_154 (c : Fin 32) : ∃w,BaseWitnessCheck 154 c.val true w := by
  refine ⟨packetData0961.getD c.val 0,?_⟩
  have h := packetCheck_sound 154 true 0 packetData0961 packetPass0961 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_155 (c : Fin 32) : ∃w,BaseWitnessCheck 155 c.val true w := by
  refine ⟨packetData0962.getD c.val 0,?_⟩
  have h := packetCheck_sound 155 true 0 packetData0962 packetPass0962 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_156 (c : Fin 32) : ∃w,BaseWitnessCheck 156 c.val true w := by
  refine ⟨packetData0963.getD c.val 0,?_⟩
  have h := packetCheck_sound 156 true 0 packetData0963 packetPass0963 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_157 (c : Fin 32) : ∃w,BaseWitnessCheck 157 c.val true w := by
  refine ⟨packetData0964.getD c.val 0,?_⟩
  have h := packetCheck_sound 157 true 0 packetData0964 packetPass0964 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_158 (c : Fin 32) : ∃w,BaseWitnessCheck 158 c.val true w := by
  refine ⟨packetData0965.getD c.val 0,?_⟩
  have h := packetCheck_sound 158 true 0 packetData0965 packetPass0965 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_159 (c : Fin 32) : ∃w,BaseWitnessCheck 159 c.val true w := by
  refine ⟨packetData0966.getD c.val 0,?_⟩
  have h := packetCheck_sound 159 true 0 packetData0966 packetPass0966 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_160 (c : Fin 32) : ∃w,BaseWitnessCheck 160 c.val true w := by
  refine ⟨packetData0967.getD c.val 0,?_⟩
  have h := packetCheck_sound 160 true 0 packetData0967 packetPass0967 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_161 (c : Fin 32) : ∃w,BaseWitnessCheck 161 c.val true w := by
  refine ⟨packetData0968.getD c.val 0,?_⟩
  have h := packetCheck_sound 161 true 0 packetData0968 packetPass0968 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_162 (c : Fin 32) : ∃w,BaseWitnessCheck 162 c.val true w := by
  refine ⟨packetData0969.getD c.val 0,?_⟩
  have h := packetCheck_sound 162 true 0 packetData0969 packetPass0969 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_163 (c : Fin 32) : ∃w,BaseWitnessCheck 163 c.val true w := by
  refine ⟨packetData0970.getD c.val 0,?_⟩
  have h := packetCheck_sound 163 true 0 packetData0970 packetPass0970 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_164 (c : Fin 32) : ∃w,BaseWitnessCheck 164 c.val true w := by
  refine ⟨packetData0971.getD c.val 0,?_⟩
  have h := packetCheck_sound 164 true 0 packetData0971 packetPass0971 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_165 (c : Fin 32) : ∃w,BaseWitnessCheck 165 c.val true w := by
  refine ⟨packetData0972.getD c.val 0,?_⟩
  have h := packetCheck_sound 165 true 0 packetData0972 packetPass0972 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_166 (c : Fin 32) : ∃w,BaseWitnessCheck 166 c.val true w := by
  refine ⟨packetData0973.getD c.val 0,?_⟩
  have h := packetCheck_sound 166 true 0 packetData0973 packetPass0973 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_167 (c : Fin 32) : ∃w,BaseWitnessCheck 167 c.val true w := by
  refine ⟨packetData0974.getD c.val 0,?_⟩
  have h := packetCheck_sound 167 true 0 packetData0974 packetPass0974 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_168 (c : Fin 32) : ∃w,BaseWitnessCheck 168 c.val true w := by
  refine ⟨packetData0975.getD c.val 0,?_⟩
  have h := packetCheck_sound 168 true 0 packetData0975 packetPass0975 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_169 (c : Fin 32) : ∃w,BaseWitnessCheck 169 c.val true w := by
  refine ⟨packetData0976.getD c.val 0,?_⟩
  have h := packetCheck_sound 169 true 0 packetData0976 packetPass0976 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_170 (c : Fin 32) : ∃w,BaseWitnessCheck 170 c.val true w := by
  refine ⟨packetData0977.getD c.val 0,?_⟩
  have h := packetCheck_sound 170 true 0 packetData0977 packetPass0977 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_171 (c : Fin 32) : ∃w,BaseWitnessCheck 171 c.val true w := by
  refine ⟨packetData0978.getD c.val 0,?_⟩
  have h := packetCheck_sound 171 true 0 packetData0978 packetPass0978 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_172 (c : Fin 32) : ∃w,BaseWitnessCheck 172 c.val true w := by
  refine ⟨packetData0979.getD c.val 0,?_⟩
  have h := packetCheck_sound 172 true 0 packetData0979 packetPass0979 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_173 (c : Fin 32) : ∃w,BaseWitnessCheck 173 c.val true w := by
  refine ⟨packetData0980.getD c.val 0,?_⟩
  have h := packetCheck_sound 173 true 0 packetData0980 packetPass0980 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_174 (c : Fin 32) : ∃w,BaseWitnessCheck 174 c.val true w := by
  refine ⟨packetData0981.getD c.val 0,?_⟩
  have h := packetCheck_sound 174 true 0 packetData0981 packetPass0981 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_175 (c : Fin 32) : ∃w,BaseWitnessCheck 175 c.val true w := by
  refine ⟨packetData0982.getD c.val 0,?_⟩
  have h := packetCheck_sound 175 true 0 packetData0982 packetPass0982 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_176 (c : Fin 32) : ∃w,BaseWitnessCheck 176 c.val true w := by
  refine ⟨packetData0983.getD c.val 0,?_⟩
  have h := packetCheck_sound 176 true 0 packetData0983 packetPass0983 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_177 (c : Fin 32) : ∃w,BaseWitnessCheck 177 c.val true w := by
  refine ⟨packetData0984.getD c.val 0,?_⟩
  have h := packetCheck_sound 177 true 0 packetData0984 packetPass0984 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_178 (c : Fin 32) : ∃w,BaseWitnessCheck 178 c.val true w := by
  refine ⟨packetData0985.getD c.val 0,?_⟩
  have h := packetCheck_sound 178 true 0 packetData0985 packetPass0985 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_179 (c : Fin 32) : ∃w,BaseWitnessCheck 179 c.val true w := by
  refine ⟨packetData0986.getD c.val 0,?_⟩
  have h := packetCheck_sound 179 true 0 packetData0986 packetPass0986 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_180 (c : Fin 32) : ∃w,BaseWitnessCheck 180 c.val true w := by
  refine ⟨packetData0987.getD c.val 0,?_⟩
  have h := packetCheck_sound 180 true 0 packetData0987 packetPass0987 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_181 (c : Fin 32) : ∃w,BaseWitnessCheck 181 c.val true w := by
  refine ⟨packetData0988.getD c.val 0,?_⟩
  have h := packetCheck_sound 181 true 0 packetData0988 packetPass0988 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_182 (c : Fin 32) : ∃w,BaseWitnessCheck 182 c.val true w := by
  refine ⟨packetData0989.getD c.val 0,?_⟩
  have h := packetCheck_sound 182 true 0 packetData0989 packetPass0989 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_183 (c : Fin 32) : ∃w,BaseWitnessCheck 183 c.val true w := by
  refine ⟨packetData0990.getD c.val 0,?_⟩
  have h := packetCheck_sound 183 true 0 packetData0990 packetPass0990 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_184 (c : Fin 32) : ∃w,BaseWitnessCheck 184 c.val true w := by
  refine ⟨packetData0991.getD c.val 0,?_⟩
  have h := packetCheck_sound 184 true 0 packetData0991 packetPass0991 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_185 (c : Fin 32) : ∃w,BaseWitnessCheck 185 c.val true w := by
  refine ⟨packetData0992.getD c.val 0,?_⟩
  have h := packetCheck_sound 185 true 0 packetData0992 packetPass0992 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_186 (c : Fin 32) : ∃w,BaseWitnessCheck 186 c.val true w := by
  refine ⟨packetData0993.getD c.val 0,?_⟩
  have h := packetCheck_sound 186 true 0 packetData0993 packetPass0993 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_187 (c : Fin 32) : ∃w,BaseWitnessCheck 187 c.val true w := by
  refine ⟨packetData0994.getD c.val 0,?_⟩
  have h := packetCheck_sound 187 true 0 packetData0994 packetPass0994 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_188 (c : Fin 32) : ∃w,BaseWitnessCheck 188 c.val true w := by
  refine ⟨packetData0995.getD c.val 0,?_⟩
  have h := packetCheck_sound 188 true 0 packetData0995 packetPass0995 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_189 (c : Fin 32) : ∃w,BaseWitnessCheck 189 c.val true w := by
  refine ⟨packetData0996.getD c.val 0,?_⟩
  have h := packetCheck_sound 189 true 0 packetData0996 packetPass0996 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_190 (c : Fin 32) : ∃w,BaseWitnessCheck 190 c.val true w := by
  refine ⟨packetData0997.getD c.val 0,?_⟩
  have h := packetCheck_sound 190 true 0 packetData0997 packetPass0997 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_191 (c : Fin 32) : ∃w,BaseWitnessCheck 191 c.val true w := by
  refine ⟨packetData0998.getD c.val 0,?_⟩
  have h := packetCheck_sound 191 true 0 packetData0998 packetPass0998 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_192 (c : Fin 32) : ∃w,BaseWitnessCheck 192 c.val true w := by
  refine ⟨packetData0999.getD c.val 0,?_⟩
  have h := packetCheck_sound 192 true 0 packetData0999 packetPass0999 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_193 (c : Fin 32) : ∃w,BaseWitnessCheck 193 c.val true w := by
  refine ⟨packetData1000.getD c.val 0,?_⟩
  have h := packetCheck_sound 193 true 0 packetData1000 packetPass1000 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_194 (c : Fin 32) : ∃w,BaseWitnessCheck 194 c.val true w := by
  refine ⟨packetData1001.getD c.val 0,?_⟩
  have h := packetCheck_sound 194 true 0 packetData1001 packetPass1001 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_195 (c : Fin 32) : ∃w,BaseWitnessCheck 195 c.val true w := by
  refine ⟨packetData1002.getD c.val 0,?_⟩
  have h := packetCheck_sound 195 true 0 packetData1002 packetPass1002 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_196 (c : Fin 32) : ∃w,BaseWitnessCheck 196 c.val true w := by
  refine ⟨packetData1003.getD c.val 0,?_⟩
  have h := packetCheck_sound 196 true 0 packetData1003 packetPass1003 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_197 (c : Fin 32) : ∃w,BaseWitnessCheck 197 c.val true w := by
  refine ⟨packetData1004.getD c.val 0,?_⟩
  have h := packetCheck_sound 197 true 0 packetData1004 packetPass1004 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_198 (c : Fin 32) : ∃w,BaseWitnessCheck 198 c.val true w := by
  refine ⟨packetData1005.getD c.val 0,?_⟩
  have h := packetCheck_sound 198 true 0 packetData1005 packetPass1005 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_199 (c : Fin 32) : ∃w,BaseWitnessCheck 199 c.val true w := by
  refine ⟨packetData1006.getD c.val 0,?_⟩
  have h := packetCheck_sound 199 true 0 packetData1006 packetPass1006 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_200 (c : Fin 32) : ∃w,BaseWitnessCheck 200 c.val true w := by
  refine ⟨packetData1007.getD c.val 0,?_⟩
  have h := packetCheck_sound 200 true 0 packetData1007 packetPass1007 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_201 (c : Fin 32) : ∃w,BaseWitnessCheck 201 c.val true w := by
  refine ⟨packetData1008.getD c.val 0,?_⟩
  have h := packetCheck_sound 201 true 0 packetData1008 packetPass1008 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_202 (c : Fin 32) : ∃w,BaseWitnessCheck 202 c.val true w := by
  refine ⟨packetData1009.getD c.val 0,?_⟩
  have h := packetCheck_sound 202 true 0 packetData1009 packetPass1009 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_203 (c : Fin 32) : ∃w,BaseWitnessCheck 203 c.val true w := by
  refine ⟨packetData1010.getD c.val 0,?_⟩
  have h := packetCheck_sound 203 true 0 packetData1010 packetPass1010 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_204 (c : Fin 32) : ∃w,BaseWitnessCheck 204 c.val true w := by
  refine ⟨packetData0020.getD c.val 0,?_⟩
  have h := packetCheck_sound 204 true 0 packetData0020 packetPass0020 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_205 (c : Fin 32) : ∃w,BaseWitnessCheck 205 c.val true w := by
  refine ⟨packetData1011.getD c.val 0,?_⟩
  have h := packetCheck_sound 205 true 0 packetData1011 packetPass1011 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_206 (c : Fin 32) : ∃w,BaseWitnessCheck 206 c.val true w := by
  refine ⟨packetData1012.getD c.val 0,?_⟩
  have h := packetCheck_sound 206 true 0 packetData1012 packetPass1012 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_207 (c : Fin 32) : ∃w,BaseWitnessCheck 207 c.val true w := by
  refine ⟨packetData1013.getD c.val 0,?_⟩
  have h := packetCheck_sound 207 true 0 packetData1013 packetPass1013 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_208 (c : Fin 32) : ∃w,BaseWitnessCheck 208 c.val true w := by
  refine ⟨packetData1014.getD c.val 0,?_⟩
  have h := packetCheck_sound 208 true 0 packetData1014 packetPass1014 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_209 (c : Fin 32) : ∃w,BaseWitnessCheck 209 c.val true w := by
  refine ⟨packetData1015.getD c.val 0,?_⟩
  have h := packetCheck_sound 209 true 0 packetData1015 packetPass1015 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_210 (c : Fin 32) : ∃w,BaseWitnessCheck 210 c.val true w := by
  refine ⟨packetData1016.getD c.val 0,?_⟩
  have h := packetCheck_sound 210 true 0 packetData1016 packetPass1016 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_211 (c : Fin 32) : ∃w,BaseWitnessCheck 211 c.val true w := by
  refine ⟨packetData1017.getD c.val 0,?_⟩
  have h := packetCheck_sound 211 true 0 packetData1017 packetPass1017 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_212 (c : Fin 32) : ∃w,BaseWitnessCheck 212 c.val true w := by
  refine ⟨packetData1018.getD c.val 0,?_⟩
  have h := packetCheck_sound 212 true 0 packetData1018 packetPass1018 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_213 (c : Fin 32) : ∃w,BaseWitnessCheck 213 c.val true w := by
  refine ⟨packetData1019.getD c.val 0,?_⟩
  have h := packetCheck_sound 213 true 0 packetData1019 packetPass1019 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_214 (c : Fin 32) : ∃w,BaseWitnessCheck 214 c.val true w := by
  refine ⟨packetData1020.getD c.val 0,?_⟩
  have h := packetCheck_sound 214 true 0 packetData1020 packetPass1020 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_215 (c : Fin 32) : ∃w,BaseWitnessCheck 215 c.val true w := by
  refine ⟨packetData1021.getD c.val 0,?_⟩
  have h := packetCheck_sound 215 true 0 packetData1021 packetPass1021 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_216 (c : Fin 32) : ∃w,BaseWitnessCheck 216 c.val true w := by
  refine ⟨packetData1022.getD c.val 0,?_⟩
  have h := packetCheck_sound 216 true 0 packetData1022 packetPass1022 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_217 (c : Fin 32) : ∃w,BaseWitnessCheck 217 c.val true w := by
  refine ⟨packetData1023.getD c.val 0,?_⟩
  have h := packetCheck_sound 217 true 0 packetData1023 packetPass1023 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_218 (c : Fin 32) : ∃w,BaseWitnessCheck 218 c.val true w := by
  refine ⟨packetData1024.getD c.val 0,?_⟩
  have h := packetCheck_sound 218 true 0 packetData1024 packetPass1024 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_219 (c : Fin 32) : ∃w,BaseWitnessCheck 219 c.val true w := by
  refine ⟨packetData1025.getD c.val 0,?_⟩
  have h := packetCheck_sound 219 true 0 packetData1025 packetPass1025 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_220 (c : Fin 32) : ∃w,BaseWitnessCheck 220 c.val true w := by
  refine ⟨packetData1026.getD c.val 0,?_⟩
  have h := packetCheck_sound 220 true 0 packetData1026 packetPass1026 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_221 (c : Fin 32) : ∃w,BaseWitnessCheck 221 c.val true w := by
  refine ⟨packetData1027.getD c.val 0,?_⟩
  have h := packetCheck_sound 221 true 0 packetData1027 packetPass1027 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_222 (c : Fin 32) : ∃w,BaseWitnessCheck 222 c.val true w := by
  refine ⟨packetData1028.getD c.val 0,?_⟩
  have h := packetCheck_sound 222 true 0 packetData1028 packetPass1028 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_223 (c : Fin 32) : ∃w,BaseWitnessCheck 223 c.val true w := by
  refine ⟨packetData1029.getD c.val 0,?_⟩
  have h := packetCheck_sound 223 true 0 packetData1029 packetPass1029 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_224 (c : Fin 32) : ∃w,BaseWitnessCheck 224 c.val true w := by
  refine ⟨packetData1030.getD c.val 0,?_⟩
  have h := packetCheck_sound 224 true 0 packetData1030 packetPass1030 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_225 (c : Fin 32) : ∃w,BaseWitnessCheck 225 c.val true w := by
  refine ⟨packetData1031.getD c.val 0,?_⟩
  have h := packetCheck_sound 225 true 0 packetData1031 packetPass1031 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_226 (c : Fin 32) : ∃w,BaseWitnessCheck 226 c.val true w := by
  refine ⟨packetData1032.getD c.val 0,?_⟩
  have h := packetCheck_sound 226 true 0 packetData1032 packetPass1032 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_227 (c : Fin 32) : ∃w,BaseWitnessCheck 227 c.val true w := by
  refine ⟨packetData1033.getD c.val 0,?_⟩
  have h := packetCheck_sound 227 true 0 packetData1033 packetPass1033 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_228 (c : Fin 32) : ∃w,BaseWitnessCheck 228 c.val true w := by
  refine ⟨packetData1034.getD c.val 0,?_⟩
  have h := packetCheck_sound 228 true 0 packetData1034 packetPass1034 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_229 (c : Fin 32) : ∃w,BaseWitnessCheck 229 c.val true w := by
  refine ⟨packetData1035.getD c.val 0,?_⟩
  have h := packetCheck_sound 229 true 0 packetData1035 packetPass1035 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_230 (c : Fin 32) : ∃w,BaseWitnessCheck 230 c.val true w := by
  refine ⟨packetData1036.getD c.val 0,?_⟩
  have h := packetCheck_sound 230 true 0 packetData1036 packetPass1036 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_231 (c : Fin 32) : ∃w,BaseWitnessCheck 231 c.val true w := by
  refine ⟨packetData1037.getD c.val 0,?_⟩
  have h := packetCheck_sound 231 true 0 packetData1037 packetPass1037 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_232 (c : Fin 32) : ∃w,BaseWitnessCheck 232 c.val true w := by
  refine ⟨packetData1038.getD c.val 0,?_⟩
  have h := packetCheck_sound 232 true 0 packetData1038 packetPass1038 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_233 (c : Fin 32) : ∃w,BaseWitnessCheck 233 c.val true w := by
  refine ⟨packetData1039.getD c.val 0,?_⟩
  have h := packetCheck_sound 233 true 0 packetData1039 packetPass1039 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_234 (c : Fin 32) : ∃w,BaseWitnessCheck 234 c.val true w := by
  refine ⟨packetData1040.getD c.val 0,?_⟩
  have h := packetCheck_sound 234 true 0 packetData1040 packetPass1040 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_235 (c : Fin 32) : ∃w,BaseWitnessCheck 235 c.val true w := by
  refine ⟨packetData1041.getD c.val 0,?_⟩
  have h := packetCheck_sound 235 true 0 packetData1041 packetPass1041 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_236 (c : Fin 32) : ∃w,BaseWitnessCheck 236 c.val true w := by
  refine ⟨packetData0021.getD c.val 0,?_⟩
  have h := packetCheck_sound 236 true 0 packetData0021 packetPass0021 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_237 (c : Fin 32) : ∃w,BaseWitnessCheck 237 c.val true w := by
  refine ⟨packetData1042.getD c.val 0,?_⟩
  have h := packetCheck_sound 237 true 0 packetData1042 packetPass1042 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_238 (c : Fin 32) : ∃w,BaseWitnessCheck 238 c.val true w := by
  refine ⟨packetData1043.getD c.val 0,?_⟩
  have h := packetCheck_sound 238 true 0 packetData1043 packetPass1043 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_239 (c : Fin 32) : ∃w,BaseWitnessCheck 239 c.val true w := by
  refine ⟨packetData1044.getD c.val 0,?_⟩
  have h := packetCheck_sound 239 true 0 packetData1044 packetPass1044 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_240 (c : Fin 32) : ∃w,BaseWitnessCheck 240 c.val true w := by
  refine ⟨packetData1045.getD c.val 0,?_⟩
  have h := packetCheck_sound 240 true 0 packetData1045 packetPass1045 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_241 (c : Fin 32) : ∃w,BaseWitnessCheck 241 c.val true w := by
  refine ⟨packetData1046.getD c.val 0,?_⟩
  have h := packetCheck_sound 241 true 0 packetData1046 packetPass1046 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_242 (c : Fin 32) : ∃w,BaseWitnessCheck 242 c.val true w := by
  refine ⟨packetData1047.getD c.val 0,?_⟩
  have h := packetCheck_sound 242 true 0 packetData1047 packetPass1047 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_243 (c : Fin 32) : ∃w,BaseWitnessCheck 243 c.val true w := by
  refine ⟨packetData1048.getD c.val 0,?_⟩
  have h := packetCheck_sound 243 true 0 packetData1048 packetPass1048 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_244 (c : Fin 32) : ∃w,BaseWitnessCheck 244 c.val true w := by
  refine ⟨packetData1049.getD c.val 0,?_⟩
  have h := packetCheck_sound 244 true 0 packetData1049 packetPass1049 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_245 (c : Fin 32) : ∃w,BaseWitnessCheck 245 c.val true w := by
  refine ⟨packetData1050.getD c.val 0,?_⟩
  have h := packetCheck_sound 245 true 0 packetData1050 packetPass1050 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_246 (c : Fin 32) : ∃w,BaseWitnessCheck 246 c.val true w := by
  refine ⟨packetData1051.getD c.val 0,?_⟩
  have h := packetCheck_sound 246 true 0 packetData1051 packetPass1051 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_247 (c : Fin 32) : ∃w,BaseWitnessCheck 247 c.val true w := by
  refine ⟨packetData1052.getD c.val 0,?_⟩
  have h := packetCheck_sound 247 true 0 packetData1052 packetPass1052 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_248 (c : Fin 32) : ∃w,BaseWitnessCheck 248 c.val true w := by
  refine ⟨packetData0022.getD c.val 0,?_⟩
  have h := packetCheck_sound 248 true 0 packetData0022 packetPass0022 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_249 (c : Fin 32) : ∃w,BaseWitnessCheck 249 c.val true w := by
  refine ⟨packetData1053.getD c.val 0,?_⟩
  have h := packetCheck_sound 249 true 0 packetData1053 packetPass1053 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_250 (c : Fin 32) : ∃w,BaseWitnessCheck 250 c.val true w := by
  refine ⟨packetData1054.getD c.val 0,?_⟩
  have h := packetCheck_sound 250 true 0 packetData1054 packetPass1054 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_251 (c : Fin 32) : ∃w,BaseWitnessCheck 251 c.val true w := by
  refine ⟨packetData1055.getD c.val 0,?_⟩
  have h := packetCheck_sound 251 true 0 packetData1055 packetPass1055 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_252 (c : Fin 32) : ∃w,BaseWitnessCheck 252 c.val true w := by
  refine ⟨packetData1056.getD c.val 0,?_⟩
  have h := packetCheck_sound 252 true 0 packetData1056 packetPass1056 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_253 (c : Fin 32) : ∃w,BaseWitnessCheck 253 c.val true w := by
  refine ⟨packetData1057.getD c.val 0,?_⟩
  have h := packetCheck_sound 253 true 0 packetData1057 packetPass1057 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_254 (c : Fin 32) : ∃w,BaseWitnessCheck 254 c.val true w := by
  refine ⟨packetData1058.getD c.val 0,?_⟩
  have h := packetCheck_sound 254 true 0 packetData1058 packetPass1058 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_255 (c : Fin 32) : ∃w,BaseWitnessCheck 255 c.val true w := by
  refine ⟨packetData1059.getD c.val 0,?_⟩
  have h := packetCheck_sound 255 true 0 packetData1059 packetPass1059 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_256 (c : Fin 32) : ∃w,BaseWitnessCheck 256 c.val true w := by
  refine ⟨packetData1060.getD c.val 0,?_⟩
  have h := packetCheck_sound 256 true 0 packetData1060 packetPass1060 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_257 (c : Fin 32) : ∃w,BaseWitnessCheck 257 c.val true w := by
  refine ⟨packetData1061.getD c.val 0,?_⟩
  have h := packetCheck_sound 257 true 0 packetData1061 packetPass1061 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_258 (c : Fin 32) : ∃w,BaseWitnessCheck 258 c.val true w := by
  refine ⟨packetData1062.getD c.val 0,?_⟩
  have h := packetCheck_sound 258 true 0 packetData1062 packetPass1062 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_259 (c : Fin 32) : ∃w,BaseWitnessCheck 259 c.val true w := by
  refine ⟨packetData1063.getD c.val 0,?_⟩
  have h := packetCheck_sound 259 true 0 packetData1063 packetPass1063 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_260 (c : Fin 32) : ∃w,BaseWitnessCheck 260 c.val true w := by
  refine ⟨packetData1064.getD c.val 0,?_⟩
  have h := packetCheck_sound 260 true 0 packetData1064 packetPass1064 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_261 (c : Fin 32) : ∃w,BaseWitnessCheck 261 c.val true w := by
  refine ⟨packetData1065.getD c.val 0,?_⟩
  have h := packetCheck_sound 261 true 0 packetData1065 packetPass1065 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_262 (c : Fin 32) : ∃w,BaseWitnessCheck 262 c.val true w := by
  refine ⟨packetData1066.getD c.val 0,?_⟩
  have h := packetCheck_sound 262 true 0 packetData1066 packetPass1066 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_263 (c : Fin 32) : ∃w,BaseWitnessCheck 263 c.val true w := by
  refine ⟨packetData1067.getD c.val 0,?_⟩
  have h := packetCheck_sound 263 true 0 packetData1067 packetPass1067 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_264 (c : Fin 32) : ∃w,BaseWitnessCheck 264 c.val true w := by
  refine ⟨packetData1068.getD c.val 0,?_⟩
  have h := packetCheck_sound 264 true 0 packetData1068 packetPass1068 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_265 (c : Fin 32) : ∃w,BaseWitnessCheck 265 c.val true w := by
  refine ⟨packetData1069.getD c.val 0,?_⟩
  have h := packetCheck_sound 265 true 0 packetData1069 packetPass1069 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_266 (c : Fin 32) : ∃w,BaseWitnessCheck 266 c.val true w := by
  refine ⟨packetData1070.getD c.val 0,?_⟩
  have h := packetCheck_sound 266 true 0 packetData1070 packetPass1070 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_267 (c : Fin 32) : ∃w,BaseWitnessCheck 267 c.val true w := by
  refine ⟨packetData1071.getD c.val 0,?_⟩
  have h := packetCheck_sound 267 true 0 packetData1071 packetPass1071 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_268 (c : Fin 32) : ∃w,BaseWitnessCheck 268 c.val true w := by
  refine ⟨packetData1072.getD c.val 0,?_⟩
  have h := packetCheck_sound 268 true 0 packetData1072 packetPass1072 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_269 (c : Fin 32) : ∃w,BaseWitnessCheck 269 c.val true w := by
  refine ⟨packetData1073.getD c.val 0,?_⟩
  have h := packetCheck_sound 269 true 0 packetData1073 packetPass1073 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_270 (c : Fin 32) : ∃w,BaseWitnessCheck 270 c.val true w := by
  refine ⟨packetData1074.getD c.val 0,?_⟩
  have h := packetCheck_sound 270 true 0 packetData1074 packetPass1074 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_271 (c : Fin 32) : ∃w,BaseWitnessCheck 271 c.val true w := by
  refine ⟨packetData1075.getD c.val 0,?_⟩
  have h := packetCheck_sound 271 true 0 packetData1075 packetPass1075 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_272 (c : Fin 32) : ∃w,BaseWitnessCheck 272 c.val true w := by
  refine ⟨packetData1076.getD c.val 0,?_⟩
  have h := packetCheck_sound 272 true 0 packetData1076 packetPass1076 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_273 (c : Fin 32) : ∃w,BaseWitnessCheck 273 c.val true w := by
  refine ⟨packetData1077.getD c.val 0,?_⟩
  have h := packetCheck_sound 273 true 0 packetData1077 packetPass1077 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_274 (c : Fin 32) : ∃w,BaseWitnessCheck 274 c.val true w := by
  refine ⟨packetData1078.getD c.val 0,?_⟩
  have h := packetCheck_sound 274 true 0 packetData1078 packetPass1078 c.val c.isLt
  simpa only [Nat.zero_add] using h

 theorem covered_1_275 (c : Fin 32) : ∃w,BaseWitnessCheck 275 c.val true w := by
  refine ⟨packetData1079.getD c.val 0,?_⟩
  have h := packetCheck_sound 275 true 0 packetData1079 packetPass1079 c.val c.isLt
  simpa only [Nat.zero_add] using h

 def packets_1_276 : Fin 8 → Array Nat := ![packetData1080,packetData1081,packetData1082,packetData1083,packetData1084,packetData1085,packetData1086,packetData1087]
 theorem packets_size_1_276 : ∀p,(packets_1_276 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_276 : ∀p,packetCheck 276 true (p.val*64) (packets_1_276 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1080
  · exact packetPass1081
  · exact packetPass1082
  · exact packetPass1083
  · exact packetPass1084
  · exact packetPass1085
  · exact packetPass1086
  · exact packetPass1087
 theorem covered_1_276 (c : Fin 512) : ∃w,BaseWitnessCheck 276 c.val true w :=
  packet_coverage 276 true 512 8 rfl packets_1_276 packets_size_1_276 packets_pass_1_276 c

 def packets_1_277 : Fin 8 → Array Nat := ![packetData1088,packetData1089,packetData1090,packetData1091,packetData1092,packetData1093,packetData1094,packetData1095]
 theorem packets_size_1_277 : ∀p,(packets_1_277 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_277 : ∀p,packetCheck 277 true (p.val*64) (packets_1_277 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1088
  · exact packetPass1089
  · exact packetPass1090
  · exact packetPass1091
  · exact packetPass1092
  · exact packetPass1093
  · exact packetPass1094
  · exact packetPass1095
 theorem covered_1_277 (c : Fin 512) : ∃w,BaseWitnessCheck 277 c.val true w :=
  packet_coverage 277 true 512 8 rfl packets_1_277 packets_size_1_277 packets_pass_1_277 c

 def packets_1_278 : Fin 8 → Array Nat := ![packetData1096,packetData1097,packetData1098,packetData1099,packetData1100,packetData1101,packetData1102,packetData1103]
 theorem packets_size_1_278 : ∀p,(packets_1_278 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_278 : ∀p,packetCheck 278 true (p.val*64) (packets_1_278 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1096
  · exact packetPass1097
  · exact packetPass1098
  · exact packetPass1099
  · exact packetPass1100
  · exact packetPass1101
  · exact packetPass1102
  · exact packetPass1103
 theorem covered_1_278 (c : Fin 512) : ∃w,BaseWitnessCheck 278 c.val true w :=
  packet_coverage 278 true 512 8 rfl packets_1_278 packets_size_1_278 packets_pass_1_278 c

 def packets_1_279 : Fin 8 → Array Nat := ![packetData1104,packetData1105,packetData1106,packetData1107,packetData1108,packetData1109,packetData1110,packetData1111]
 theorem packets_size_1_279 : ∀p,(packets_1_279 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_279 : ∀p,packetCheck 279 true (p.val*64) (packets_1_279 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1104
  · exact packetPass1105
  · exact packetPass1106
  · exact packetPass1107
  · exact packetPass1108
  · exact packetPass1109
  · exact packetPass1110
  · exact packetPass1111
 theorem covered_1_279 (c : Fin 512) : ∃w,BaseWitnessCheck 279 c.val true w :=
  packet_coverage 279 true 512 8 rfl packets_1_279 packets_size_1_279 packets_pass_1_279 c

 def packets_1_280 : Fin 8 → Array Nat := ![packetData1112,packetData0023,packetData1113,packetData1114,packetData1115,packetData1116,packetData1117,packetData1118]
 theorem packets_size_1_280 : ∀p,(packets_1_280 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_280 : ∀p,packetCheck 280 true (p.val*64) (packets_1_280 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1112
  · exact packetPass0023
  · exact packetPass1113
  · exact packetPass1114
  · exact packetPass1115
  · exact packetPass1116
  · exact packetPass1117
  · exact packetPass1118
 theorem covered_1_280 (c : Fin 512) : ∃w,BaseWitnessCheck 280 c.val true w :=
  packet_coverage 280 true 512 8 rfl packets_1_280 packets_size_1_280 packets_pass_1_280 c

 def packets_1_281 : Fin 8 → Array Nat := ![packetData1119,packetData1120,packetData1121,packetData1122,packetData1123,packetData1124,packetData1125,packetData1126]
 theorem packets_size_1_281 : ∀p,(packets_1_281 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_281 : ∀p,packetCheck 281 true (p.val*64) (packets_1_281 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1119
  · exact packetPass1120
  · exact packetPass1121
  · exact packetPass1122
  · exact packetPass1123
  · exact packetPass1124
  · exact packetPass1125
  · exact packetPass1126
 theorem covered_1_281 (c : Fin 512) : ∃w,BaseWitnessCheck 281 c.val true w :=
  packet_coverage 281 true 512 8 rfl packets_1_281 packets_size_1_281 packets_pass_1_281 c

 def packets_1_282 : Fin 8 → Array Nat := ![packetData1127,packetData1128,packetData1129,packetData1130,packetData1131,packetData1132,packetData1133,packetData1134]
 theorem packets_size_1_282 : ∀p,(packets_1_282 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_282 : ∀p,packetCheck 282 true (p.val*64) (packets_1_282 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1127
  · exact packetPass1128
  · exact packetPass1129
  · exact packetPass1130
  · exact packetPass1131
  · exact packetPass1132
  · exact packetPass1133
  · exact packetPass1134
 theorem covered_1_282 (c : Fin 512) : ∃w,BaseWitnessCheck 282 c.val true w :=
  packet_coverage 282 true 512 8 rfl packets_1_282 packets_size_1_282 packets_pass_1_282 c

 def packets_1_283 : Fin 8 → Array Nat := ![packetData1135,packetData1136,packetData1137,packetData1138,packetData1139,packetData1140,packetData1141,packetData1142]
 theorem packets_size_1_283 : ∀p,(packets_1_283 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_283 : ∀p,packetCheck 283 true (p.val*64) (packets_1_283 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1135
  · exact packetPass1136
  · exact packetPass1137
  · exact packetPass1138
  · exact packetPass1139
  · exact packetPass1140
  · exact packetPass1141
  · exact packetPass1142
 theorem covered_1_283 (c : Fin 512) : ∃w,BaseWitnessCheck 283 c.val true w :=
  packet_coverage 283 true 512 8 rfl packets_1_283 packets_size_1_283 packets_pass_1_283 c

 def packets_1_284 : Fin 8 → Array Nat := ![packetData1143,packetData0024,packetData1144,packetData1145,packetData1146,packetData1147,packetData1148,packetData1149]
 theorem packets_size_1_284 : ∀p,(packets_1_284 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_284 : ∀p,packetCheck 284 true (p.val*64) (packets_1_284 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1143
  · exact packetPass0024
  · exact packetPass1144
  · exact packetPass1145
  · exact packetPass1146
  · exact packetPass1147
  · exact packetPass1148
  · exact packetPass1149
 theorem covered_1_284 (c : Fin 512) : ∃w,BaseWitnessCheck 284 c.val true w :=
  packet_coverage 284 true 512 8 rfl packets_1_284 packets_size_1_284 packets_pass_1_284 c

 def packets_1_285 : Fin 8 → Array Nat := ![packetData1150,packetData1151,packetData1152,packetData1153,packetData1154,packetData1155,packetData1156,packetData1157]
 theorem packets_size_1_285 : ∀p,(packets_1_285 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_285 : ∀p,packetCheck 285 true (p.val*64) (packets_1_285 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1150
  · exact packetPass1151
  · exact packetPass1152
  · exact packetPass1153
  · exact packetPass1154
  · exact packetPass1155
  · exact packetPass1156
  · exact packetPass1157
 theorem covered_1_285 (c : Fin 512) : ∃w,BaseWitnessCheck 285 c.val true w :=
  packet_coverage 285 true 512 8 rfl packets_1_285 packets_size_1_285 packets_pass_1_285 c

 def packets_1_286 : Fin 8 → Array Nat := ![packetData1158,packetData1159,packetData1160,packetData1161,packetData0025,packetData1162,packetData1163,packetData1164]
 theorem packets_size_1_286 : ∀p,(packets_1_286 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_286 : ∀p,packetCheck 286 true (p.val*64) (packets_1_286 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1158
  · exact packetPass1159
  · exact packetPass1160
  · exact packetPass1161
  · exact packetPass0025
  · exact packetPass1162
  · exact packetPass1163
  · exact packetPass1164
 theorem covered_1_286 (c : Fin 512) : ∃w,BaseWitnessCheck 286 c.val true w :=
  packet_coverage 286 true 512 8 rfl packets_1_286 packets_size_1_286 packets_pass_1_286 c

 def packets_1_287 : Fin 8 → Array Nat := ![packetData1165,packetData1166,packetData1167,packetData1168,packetData1169,packetData1170,packetData1171,packetData1172]
 theorem packets_size_1_287 : ∀p,(packets_1_287 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_287 : ∀p,packetCheck 287 true (p.val*64) (packets_1_287 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1165
  · exact packetPass1166
  · exact packetPass1167
  · exact packetPass1168
  · exact packetPass1169
  · exact packetPass1170
  · exact packetPass1171
  · exact packetPass1172
 theorem covered_1_287 (c : Fin 512) : ∃w,BaseWitnessCheck 287 c.val true w :=
  packet_coverage 287 true 512 8 rfl packets_1_287 packets_size_1_287 packets_pass_1_287 c

 def packets_1_288 : Fin 8 → Array Nat := ![packetData1173,packetData1174,packetData1175,packetData1176,packetData1177,packetData1178,packetData1179,packetData1180]
 theorem packets_size_1_288 : ∀p,(packets_1_288 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_288 : ∀p,packetCheck 288 true (p.val*64) (packets_1_288 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1173
  · exact packetPass1174
  · exact packetPass1175
  · exact packetPass1176
  · exact packetPass1177
  · exact packetPass1178
  · exact packetPass1179
  · exact packetPass1180
 theorem covered_1_288 (c : Fin 512) : ∃w,BaseWitnessCheck 288 c.val true w :=
  packet_coverage 288 true 512 8 rfl packets_1_288 packets_size_1_288 packets_pass_1_288 c

 def packets_1_289 : Fin 8 → Array Nat := ![packetData1181,packetData1182,packetData1183,packetData1184,packetData1185,packetData1186,packetData1187,packetData1188]
 theorem packets_size_1_289 : ∀p,(packets_1_289 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_289 : ∀p,packetCheck 289 true (p.val*64) (packets_1_289 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1181
  · exact packetPass1182
  · exact packetPass1183
  · exact packetPass1184
  · exact packetPass1185
  · exact packetPass1186
  · exact packetPass1187
  · exact packetPass1188
 theorem covered_1_289 (c : Fin 512) : ∃w,BaseWitnessCheck 289 c.val true w :=
  packet_coverage 289 true 512 8 rfl packets_1_289 packets_size_1_289 packets_pass_1_289 c

 def packets_1_290 : Fin 8 → Array Nat := ![packetData1189,packetData1190,packetData1191,packetData1192,packetData1193,packetData1194,packetData1195,packetData1196]
 theorem packets_size_1_290 : ∀p,(packets_1_290 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_290 : ∀p,packetCheck 290 true (p.val*64) (packets_1_290 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1189
  · exact packetPass1190
  · exact packetPass1191
  · exact packetPass1192
  · exact packetPass1193
  · exact packetPass1194
  · exact packetPass1195
  · exact packetPass1196
 theorem covered_1_290 (c : Fin 512) : ∃w,BaseWitnessCheck 290 c.val true w :=
  packet_coverage 290 true 512 8 rfl packets_1_290 packets_size_1_290 packets_pass_1_290 c

 def packets_1_291 : Fin 8 → Array Nat := ![packetData1197,packetData1198,packetData1199,packetData1200,packetData1201,packetData1202,packetData1203,packetData1204]
 theorem packets_size_1_291 : ∀p,(packets_1_291 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_291 : ∀p,packetCheck 291 true (p.val*64) (packets_1_291 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1197
  · exact packetPass1198
  · exact packetPass1199
  · exact packetPass1200
  · exact packetPass1201
  · exact packetPass1202
  · exact packetPass1203
  · exact packetPass1204
 theorem covered_1_291 (c : Fin 512) : ∃w,BaseWitnessCheck 291 c.val true w :=
  packet_coverage 291 true 512 8 rfl packets_1_291 packets_size_1_291 packets_pass_1_291 c

 def packets_1_292 : Fin 8 → Array Nat := ![packetData1205,packetData0026,packetData1206,packetData1207,packetData1208,packetData1209,packetData1210,packetData1211]
 theorem packets_size_1_292 : ∀p,(packets_1_292 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_292 : ∀p,packetCheck 292 true (p.val*64) (packets_1_292 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1205
  · exact packetPass0026
  · exact packetPass1206
  · exact packetPass1207
  · exact packetPass1208
  · exact packetPass1209
  · exact packetPass1210
  · exact packetPass1211
 theorem covered_1_292 (c : Fin 512) : ∃w,BaseWitnessCheck 292 c.val true w :=
  packet_coverage 292 true 512 8 rfl packets_1_292 packets_size_1_292 packets_pass_1_292 c

 def packets_1_293 : Fin 8 → Array Nat := ![packetData1212,packetData1213,packetData1214,packetData1215,packetData1216,packetData1217,packetData1218,packetData1219]
 theorem packets_size_1_293 : ∀p,(packets_1_293 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_293 : ∀p,packetCheck 293 true (p.val*64) (packets_1_293 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1212
  · exact packetPass1213
  · exact packetPass1214
  · exact packetPass1215
  · exact packetPass1216
  · exact packetPass1217
  · exact packetPass1218
  · exact packetPass1219
 theorem covered_1_293 (c : Fin 512) : ∃w,BaseWitnessCheck 293 c.val true w :=
  packet_coverage 293 true 512 8 rfl packets_1_293 packets_size_1_293 packets_pass_1_293 c

 def packets_1_294 : Fin 8 → Array Nat := ![packetData1220,packetData1221,packetData1222,packetData1223,packetData0027,packetData1224,packetData1225,packetData1226]
 theorem packets_size_1_294 : ∀p,(packets_1_294 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_294 : ∀p,packetCheck 294 true (p.val*64) (packets_1_294 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1220
  · exact packetPass1221
  · exact packetPass1222
  · exact packetPass1223
  · exact packetPass0027
  · exact packetPass1224
  · exact packetPass1225
  · exact packetPass1226
 theorem covered_1_294 (c : Fin 512) : ∃w,BaseWitnessCheck 294 c.val true w :=
  packet_coverage 294 true 512 8 rfl packets_1_294 packets_size_1_294 packets_pass_1_294 c

 def packets_1_295 : Fin 8 → Array Nat := ![packetData1227,packetData1228,packetData1229,packetData1230,packetData1231,packetData1232,packetData1233,packetData1234]
 theorem packets_size_1_295 : ∀p,(packets_1_295 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_295 : ∀p,packetCheck 295 true (p.val*64) (packets_1_295 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1227
  · exact packetPass1228
  · exact packetPass1229
  · exact packetPass1230
  · exact packetPass1231
  · exact packetPass1232
  · exact packetPass1233
  · exact packetPass1234
 theorem covered_1_295 (c : Fin 512) : ∃w,BaseWitnessCheck 295 c.val true w :=
  packet_coverage 295 true 512 8 rfl packets_1_295 packets_size_1_295 packets_pass_1_295 c

 def packets_1_296 : Fin 8 → Array Nat := ![packetData1235,packetData1236,packetData1237,packetData1238,packetData1239,packetData1240,packetData1241,packetData1242]
 theorem packets_size_1_296 : ∀p,(packets_1_296 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_296 : ∀p,packetCheck 296 true (p.val*64) (packets_1_296 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1235
  · exact packetPass1236
  · exact packetPass1237
  · exact packetPass1238
  · exact packetPass1239
  · exact packetPass1240
  · exact packetPass1241
  · exact packetPass1242
 theorem covered_1_296 (c : Fin 512) : ∃w,BaseWitnessCheck 296 c.val true w :=
  packet_coverage 296 true 512 8 rfl packets_1_296 packets_size_1_296 packets_pass_1_296 c

 def packets_1_297 : Fin 8 → Array Nat := ![packetData1243,packetData1244,packetData1245,packetData1246,packetData1247,packetData1248,packetData1249,packetData1250]
 theorem packets_size_1_297 : ∀p,(packets_1_297 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_297 : ∀p,packetCheck 297 true (p.val*64) (packets_1_297 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1243
  · exact packetPass1244
  · exact packetPass1245
  · exact packetPass1246
  · exact packetPass1247
  · exact packetPass1248
  · exact packetPass1249
  · exact packetPass1250
 theorem covered_1_297 (c : Fin 512) : ∃w,BaseWitnessCheck 297 c.val true w :=
  packet_coverage 297 true 512 8 rfl packets_1_297 packets_size_1_297 packets_pass_1_297 c

 def packets_1_298 : Fin 8 → Array Nat := ![packetData1251,packetData1252,packetData1253,packetData1254,packetData1255,packetData0028,packetData1256,packetData1257]
 theorem packets_size_1_298 : ∀p,(packets_1_298 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_298 : ∀p,packetCheck 298 true (p.val*64) (packets_1_298 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1251
  · exact packetPass1252
  · exact packetPass1253
  · exact packetPass1254
  · exact packetPass1255
  · exact packetPass0028
  · exact packetPass1256
  · exact packetPass1257
 theorem covered_1_298 (c : Fin 512) : ∃w,BaseWitnessCheck 298 c.val true w :=
  packet_coverage 298 true 512 8 rfl packets_1_298 packets_size_1_298 packets_pass_1_298 c

 def packets_1_299 : Fin 8 → Array Nat := ![packetData1258,packetData1259,packetData1260,packetData1261,packetData1262,packetData1263,packetData1264,packetData1265]
 theorem packets_size_1_299 : ∀p,(packets_1_299 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_299 : ∀p,packetCheck 299 true (p.val*64) (packets_1_299 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1258
  · exact packetPass1259
  · exact packetPass1260
  · exact packetPass1261
  · exact packetPass1262
  · exact packetPass1263
  · exact packetPass1264
  · exact packetPass1265
 theorem covered_1_299 (c : Fin 512) : ∃w,BaseWitnessCheck 299 c.val true w :=
  packet_coverage 299 true 512 8 rfl packets_1_299 packets_size_1_299 packets_pass_1_299 c

 def packets_1_300 : Fin 8 → Array Nat := ![packetData1266,packetData1267,packetData1268,packetData1269,packetData1270,packetData1271,packetData1272,packetData1273]
 theorem packets_size_1_300 : ∀p,(packets_1_300 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_300 : ∀p,packetCheck 300 true (p.val*64) (packets_1_300 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1266
  · exact packetPass1267
  · exact packetPass1268
  · exact packetPass1269
  · exact packetPass1270
  · exact packetPass1271
  · exact packetPass1272
  · exact packetPass1273
 theorem covered_1_300 (c : Fin 512) : ∃w,BaseWitnessCheck 300 c.val true w :=
  packet_coverage 300 true 512 8 rfl packets_1_300 packets_size_1_300 packets_pass_1_300 c

 def packets_1_301 : Fin 8 → Array Nat := ![packetData1274,packetData1275,packetData1276,packetData1277,packetData1278,packetData1279,packetData1280,packetData1281]
 theorem packets_size_1_301 : ∀p,(packets_1_301 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_301 : ∀p,packetCheck 301 true (p.val*64) (packets_1_301 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1274
  · exact packetPass1275
  · exact packetPass1276
  · exact packetPass1277
  · exact packetPass1278
  · exact packetPass1279
  · exact packetPass1280
  · exact packetPass1281
 theorem covered_1_301 (c : Fin 512) : ∃w,BaseWitnessCheck 301 c.val true w :=
  packet_coverage 301 true 512 8 rfl packets_1_301 packets_size_1_301 packets_pass_1_301 c

 def packets_1_302 : Fin 8 → Array Nat := ![packetData1282,packetData1283,packetData1284,packetData1285,packetData1286,packetData1287,packetData1288,packetData1289]
 theorem packets_size_1_302 : ∀p,(packets_1_302 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_302 : ∀p,packetCheck 302 true (p.val*64) (packets_1_302 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1282
  · exact packetPass1283
  · exact packetPass1284
  · exact packetPass1285
  · exact packetPass1286
  · exact packetPass1287
  · exact packetPass1288
  · exact packetPass1289
 theorem covered_1_302 (c : Fin 512) : ∃w,BaseWitnessCheck 302 c.val true w :=
  packet_coverage 302 true 512 8 rfl packets_1_302 packets_size_1_302 packets_pass_1_302 c

 def packets_1_303 : Fin 8 → Array Nat := ![packetData1290,packetData1291,packetData1292,packetData1293,packetData1294,packetData1295,packetData1296,packetData1297]
 theorem packets_size_1_303 : ∀p,(packets_1_303 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_303 : ∀p,packetCheck 303 true (p.val*64) (packets_1_303 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1290
  · exact packetPass1291
  · exact packetPass1292
  · exact packetPass1293
  · exact packetPass1294
  · exact packetPass1295
  · exact packetPass1296
  · exact packetPass1297
 theorem covered_1_303 (c : Fin 512) : ∃w,BaseWitnessCheck 303 c.val true w :=
  packet_coverage 303 true 512 8 rfl packets_1_303 packets_size_1_303 packets_pass_1_303 c

 def packets_1_304 : Fin 8 → Array Nat := ![packetData0029,packetData0030,packetData0031,packetData0032,packetData0033,packetData1298,packetData0034,packetData1299]
 theorem packets_size_1_304 : ∀p,(packets_1_304 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_304 : ∀p,packetCheck 304 true (p.val*64) (packets_1_304 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0029
  · exact packetPass0030
  · exact packetPass0031
  · exact packetPass0032
  · exact packetPass0033
  · exact packetPass1298
  · exact packetPass0034
  · exact packetPass1299
 theorem covered_1_304 (c : Fin 512) : ∃w,BaseWitnessCheck 304 c.val true w :=
  packet_coverage 304 true 512 8 rfl packets_1_304 packets_size_1_304 packets_pass_1_304 c

 def packets_1_305 : Fin 8 → Array Nat := ![packetData0035,packetData1300,packetData1301,packetData1302,packetData1303,packetData1304,packetData1305,packetData1306]
 theorem packets_size_1_305 : ∀p,(packets_1_305 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_305 : ∀p,packetCheck 305 true (p.val*64) (packets_1_305 p)=true := by
  intro p
  fin_cases p
  · exact packetPass0035
  · exact packetPass1300
  · exact packetPass1301
  · exact packetPass1302
  · exact packetPass1303
  · exact packetPass1304
  · exact packetPass1305
  · exact packetPass1306
 theorem covered_1_305 (c : Fin 512) : ∃w,BaseWitnessCheck 305 c.val true w :=
  packet_coverage 305 true 512 8 rfl packets_1_305 packets_size_1_305 packets_pass_1_305 c

 def packets_1_306 : Fin 256 → Array Nat := ![packetData1307,packetData1308,packetData1309,packetData1310,packetData1311,packetData1312,packetData1313,packetData1314,packetData1315,packetData1316,packetData1317,packetData1318,packetData1319,packetData1320,packetData1321,packetData1322,packetData1323,packetData1324,packetData1325,packetData1326,packetData1327,packetData1328,packetData1329,packetData1330,packetData1331,packetData1332,packetData1333,packetData1334,packetData1335,packetData1336,packetData1337,packetData1338,packetData1339,packetData1340,packetData1341,packetData1342,packetData1343,packetData1344,packetData1345,packetData1346,packetData1347,packetData1348,packetData0036,packetData1349,packetData1350,packetData1351,packetData1352,packetData1353,packetData1354,packetData1355,packetData1356,packetData1357,packetData1358,packetData1359,packetData1360,packetData1361,packetData1362,packetData1363,packetData1364,packetData1365,packetData1366,packetData1367,packetData1368,packetData1369,packetData1370,packetData1371,packetData1372,packetData1373,packetData1374,packetData1375,packetData1376,packetData1377,packetData1378,packetData1379,packetData1380,packetData1381,packetData1382,packetData1383,packetData1384,packetData1385,packetData1386,packetData1387,packetData1388,packetData1389,packetData1390,packetData0037,packetData1391,packetData1392,packetData1393,packetData1394,packetData1395,packetData1396,packetData1397,packetData1398,packetData1399,packetData1400,packetData1401,packetData1402,packetData1403,packetData1404,packetData1405,packetData1406,packetData1407,packetData1408,packetData1409,packetData1410,packetData1411,packetData0038,packetData1412,packetData1413,packetData0039,packetData1414,packetData1415,packetData1416,packetData1417,packetData1418,packetData1419,packetData1420,packetData1421,packetData1422,packetData1423,packetData1424,packetData0040,packetData1425,packetData1426,packetData1427,packetData1428,packetData1429,packetData1430,packetData1431,packetData1432,packetData1433,packetData1434,packetData1435,packetData1436,packetData1437,packetData1438,packetData1439,packetData0041,packetData1440,packetData1441,packetData1442,packetData1443,packetData1444,packetData1445,packetData1446,packetData1447,packetData1448,packetData1449,packetData1450,packetData1451,packetData1452,packetData1453,packetData1454,packetData1455,packetData0042,packetData1456,packetData1457,packetData0043,packetData1458,packetData1459,packetData1460,packetData0044,packetData1461,packetData1462,packetData1463,packetData1464,packetData0045,packetData0046,packetData1465,packetData0047,packetData1466,packetData1467,packetData0048,packetData1468,packetData1469,packetData1470,packetData1471,packetData1472,packetData1473,packetData1474,packetData1475,packetData0049,packetData1476,packetData1477,packetData0050,packetData1478,packetData1479,packetData1480,packetData1481,packetData1482,packetData1483,packetData1484,packetData1485,packetData1486,packetData1487,packetData1488,packetData1489,packetData1490,packetData1491,packetData1492,packetData1493,packetData1494,packetData1495,packetData1496,packetData1497,packetData1498,packetData1499,packetData1500,packetData1501,packetData1502,packetData1503,packetData1504,packetData1505,packetData1506,packetData1507,packetData1508,packetData1509,packetData0051,packetData1510,packetData1511,packetData1512,packetData1513,packetData1514,packetData1515,packetData1516,packetData1517,packetData1518,packetData1519,packetData1520,packetData0052,packetData1521,packetData1522,packetData0053,packetData1523,packetData1524,packetData1525,packetData1526,packetData1527,packetData1528,packetData1529,packetData1530,packetData1531,packetData1532,packetData1533,packetData1534,packetData1535,packetData1536,packetData1537,packetData1538,packetData1539,packetData1540,packetData1541,packetData1542,packetData1543,packetData0054]
 theorem packets_size_1_306 : ∀p,(packets_1_306 p).size=64 := by
  intro p
  fin_cases p <;> rfl
 theorem packets_pass_1_306 : ∀p,packetCheck 306 true (p.val*64) (packets_1_306 p)=true := by
  intro p
  fin_cases p
  · exact packetPass1307
  · exact packetPass1308
  · exact packetPass1309
  · exact packetPass1310
  · exact packetPass1311
  · exact packetPass1312
  · exact packetPass1313
  · exact packetPass1314
  · exact packetPass1315
  · exact packetPass1316
  · exact packetPass1317
  · exact packetPass1318
  · exact packetPass1319
  · exact packetPass1320
  · exact packetPass1321
  · exact packetPass1322
  · exact packetPass1323
  · exact packetPass1324
  · exact packetPass1325
  · exact packetPass1326
  · exact packetPass1327
  · exact packetPass1328
  · exact packetPass1329
  · exact packetPass1330
  · exact packetPass1331
  · exact packetPass1332
  · exact packetPass1333
  · exact packetPass1334
  · exact packetPass1335
  · exact packetPass1336
  · exact packetPass1337
  · exact packetPass1338
  · exact packetPass1339
  · exact packetPass1340
  · exact packetPass1341
  · exact packetPass1342
  · exact packetPass1343
  · exact packetPass1344
  · exact packetPass1345
  · exact packetPass1346
  · exact packetPass1347
  · exact packetPass1348
  · exact packetPass0036
  · exact packetPass1349
  · exact packetPass1350
  · exact packetPass1351
  · exact packetPass1352
  · exact packetPass1353
  · exact packetPass1354
  · exact packetPass1355
  · exact packetPass1356
  · exact packetPass1357
  · exact packetPass1358
  · exact packetPass1359
  · exact packetPass1360
  · exact packetPass1361
  · exact packetPass1362
  · exact packetPass1363
  · exact packetPass1364
  · exact packetPass1365
  · exact packetPass1366
  · exact packetPass1367
  · exact packetPass1368
  · exact packetPass1369
  · exact packetPass1370
  · exact packetPass1371
  · exact packetPass1372
  · exact packetPass1373
  · exact packetPass1374
  · exact packetPass1375
  · exact packetPass1376
  · exact packetPass1377
  · exact packetPass1378
  · exact packetPass1379
  · exact packetPass1380
  · exact packetPass1381
  · exact packetPass1382
  · exact packetPass1383
  · exact packetPass1384
  · exact packetPass1385
  · exact packetPass1386
  · exact packetPass1387
  · exact packetPass1388
  · exact packetPass1389
  · exact packetPass1390
  · exact packetPass0037
  · exact packetPass1391
  · exact packetPass1392
  · exact packetPass1393
  · exact packetPass1394
  · exact packetPass1395
  · exact packetPass1396
  · exact packetPass1397
  · exact packetPass1398
  · exact packetPass1399
  · exact packetPass1400
  · exact packetPass1401
  · exact packetPass1402
  · exact packetPass1403
  · exact packetPass1404
  · exact packetPass1405
  · exact packetPass1406
  · exact packetPass1407
  · exact packetPass1408
  · exact packetPass1409
  · exact packetPass1410
  · exact packetPass1411
  · exact packetPass0038
  · exact packetPass1412
  · exact packetPass1413
  · exact packetPass0039
  · exact packetPass1414
  · exact packetPass1415
  · exact packetPass1416
  · exact packetPass1417
  · exact packetPass1418
  · exact packetPass1419
  · exact packetPass1420
  · exact packetPass1421
  · exact packetPass1422
  · exact packetPass1423
  · exact packetPass1424
  · exact packetPass0040
  · exact packetPass1425
  · exact packetPass1426
  · exact packetPass1427
  · exact packetPass1428
  · exact packetPass1429
  · exact packetPass1430
  · exact packetPass1431
  · exact packetPass1432
  · exact packetPass1433
  · exact packetPass1434
  · exact packetPass1435
  · exact packetPass1436
  · exact packetPass1437
  · exact packetPass1438
  · exact packetPass1439
  · exact packetPass0041
  · exact packetPass1440
  · exact packetPass1441
  · exact packetPass1442
  · exact packetPass1443
  · exact packetPass1444
  · exact packetPass1445
  · exact packetPass1446
  · exact packetPass1447
  · exact packetPass1448
  · exact packetPass1449
  · exact packetPass1450
  · exact packetPass1451
  · exact packetPass1452
  · exact packetPass1453
  · exact packetPass1454
  · exact packetPass1455
  · exact packetPass0042
  · exact packetPass1456
  · exact packetPass1457
  · exact packetPass0043
  · exact packetPass1458
  · exact packetPass1459
  · exact packetPass1460
  · exact packetPass0044
  · exact packetPass1461
  · exact packetPass1462
  · exact packetPass1463
  · exact packetPass1464
  · exact packetPass0045
  · exact packetPass0046
  · exact packetPass1465
  · exact packetPass0047
  · exact packetPass1466
  · exact packetPass1467
  · exact packetPass0048
  · exact packetPass1468
  · exact packetPass1469
  · exact packetPass1470
  · exact packetPass1471
  · exact packetPass1472
  · exact packetPass1473
  · exact packetPass1474
  · exact packetPass1475
  · exact packetPass0049
  · exact packetPass1476
  · exact packetPass1477
  · exact packetPass0050
  · exact packetPass1478
  · exact packetPass1479
  · exact packetPass1480
  · exact packetPass1481
  · exact packetPass1482
  · exact packetPass1483
  · exact packetPass1484
  · exact packetPass1485
  · exact packetPass1486
  · exact packetPass1487
  · exact packetPass1488
  · exact packetPass1489
  · exact packetPass1490
  · exact packetPass1491
  · exact packetPass1492
  · exact packetPass1493
  · exact packetPass1494
  · exact packetPass1495
  · exact packetPass1496
  · exact packetPass1497
  · exact packetPass1498
  · exact packetPass1499
  · exact packetPass1500
  · exact packetPass1501
  · exact packetPass1502
  · exact packetPass1503
  · exact packetPass1504
  · exact packetPass1505
  · exact packetPass1506
  · exact packetPass1507
  · exact packetPass1508
  · exact packetPass1509
  · exact packetPass0051
  · exact packetPass1510
  · exact packetPass1511
  · exact packetPass1512
  · exact packetPass1513
  · exact packetPass1514
  · exact packetPass1515
  · exact packetPass1516
  · exact packetPass1517
  · exact packetPass1518
  · exact packetPass1519
  · exact packetPass1520
  · exact packetPass0052
  · exact packetPass1521
  · exact packetPass1522
  · exact packetPass0053
  · exact packetPass1523
  · exact packetPass1524
  · exact packetPass1525
  · exact packetPass1526
  · exact packetPass1527
  · exact packetPass1528
  · exact packetPass1529
  · exact packetPass1530
  · exact packetPass1531
  · exact packetPass1532
  · exact packetPass1533
  · exact packetPass1534
  · exact packetPass1535
  · exact packetPass1536
  · exact packetPass1537
  · exact packetPass1538
  · exact packetPass1539
  · exact packetPass1540
  · exact packetPass1541
  · exact packetPass1542
  · exact packetPass1543
  · exact packetPass0054
 theorem covered_1_306 (c : Fin 16384) : ∃w,BaseWitnessCheck 306 c.val true w :=
  packet_coverage 306 true 16384 256 rfl packets_1_306 packets_size_1_306 packets_pass_1_306 c

 theorem base_inputs_true (c : InputCode) : ∃w,BaseWitnessCheck c.1 c.2.val true w := by
  obtain ⟨s,c⟩ := c
  fin_cases s
  · exact covered_1_000 c
  · exact covered_1_001 c
  · exact covered_1_002 c
  · exact covered_1_003 c
  · exact covered_1_004 c
  · exact covered_1_005 c
  · exact covered_1_006 c
  · exact covered_1_007 c
  · exact covered_1_008 c
  · exact covered_1_009 c
  · exact covered_1_010 c
  · exact covered_1_011 c
  · exact covered_1_012 c
  · exact covered_1_013 c
  · exact covered_1_014 c
  · exact covered_1_015 c
  · exact covered_1_016 c
  · exact covered_1_017 c
  · exact covered_1_018 c
  · exact covered_1_019 c
  · exact covered_1_020 c
  · exact covered_1_021 c
  · exact covered_1_022 c
  · exact covered_1_023 c
  · exact covered_1_024 c
  · exact covered_1_025 c
  · exact covered_1_026 c
  · exact covered_1_027 c
  · exact covered_1_028 c
  · exact covered_1_029 c
  · exact covered_1_030 c
  · exact covered_1_031 c
  · exact covered_1_032 c
  · exact covered_1_033 c
  · exact covered_1_034 c
  · exact covered_1_035 c
  · exact covered_1_036 c
  · exact covered_1_037 c
  · exact covered_1_038 c
  · exact covered_1_039 c
  · exact covered_1_040 c
  · exact covered_1_041 c
  · exact covered_1_042 c
  · exact covered_1_043 c
  · exact covered_1_044 c
  · exact covered_1_045 c
  · exact covered_1_046 c
  · exact covered_1_047 c
  · exact covered_1_048 c
  · exact covered_1_049 c
  · exact covered_1_050 c
  · exact covered_1_051 c
  · exact covered_1_052 c
  · exact covered_1_053 c
  · exact covered_1_054 c
  · exact covered_1_055 c
  · exact covered_1_056 c
  · exact covered_1_057 c
  · exact covered_1_058 c
  · exact covered_1_059 c
  · exact covered_1_060 c
  · exact covered_1_061 c
  · exact covered_1_062 c
  · exact covered_1_063 c
  · exact covered_1_064 c
  · exact covered_1_065 c
  · exact covered_1_066 c
  · exact covered_1_067 c
  · exact covered_1_068 c
  · exact covered_1_069 c
  · exact covered_1_070 c
  · exact covered_1_071 c
  · exact covered_1_072 c
  · exact covered_1_073 c
  · exact covered_1_074 c
  · exact covered_1_075 c
  · exact covered_1_076 c
  · exact covered_1_077 c
  · exact covered_1_078 c
  · exact covered_1_079 c
  · exact covered_1_080 c
  · exact covered_1_081 c
  · exact covered_1_082 c
  · exact covered_1_083 c
  · exact covered_1_084 c
  · exact covered_1_085 c
  · exact covered_1_086 c
  · exact covered_1_087 c
  · exact covered_1_088 c
  · exact covered_1_089 c
  · exact covered_1_090 c
  · exact covered_1_091 c
  · exact covered_1_092 c
  · exact covered_1_093 c
  · exact covered_1_094 c
  · exact covered_1_095 c
  · exact covered_1_096 c
  · exact covered_1_097 c
  · exact covered_1_098 c
  · exact covered_1_099 c
  · exact covered_1_100 c
  · exact covered_1_101 c
  · exact covered_1_102 c
  · exact covered_1_103 c
  · exact covered_1_104 c
  · exact covered_1_105 c
  · exact covered_1_106 c
  · exact covered_1_107 c
  · exact covered_1_108 c
  · exact covered_1_109 c
  · exact covered_1_110 c
  · exact covered_1_111 c
  · exact covered_1_112 c
  · exact covered_1_113 c
  · exact covered_1_114 c
  · exact covered_1_115 c
  · exact covered_1_116 c
  · exact covered_1_117 c
  · exact covered_1_118 c
  · exact covered_1_119 c
  · exact covered_1_120 c
  · exact covered_1_121 c
  · exact covered_1_122 c
  · exact covered_1_123 c
  · exact covered_1_124 c
  · exact covered_1_125 c
  · exact covered_1_126 c
  · exact covered_1_127 c
  · exact covered_1_128 c
  · exact covered_1_129 c
  · exact covered_1_130 c
  · exact covered_1_131 c
  · exact covered_1_132 c
  · exact covered_1_133 c
  · exact covered_1_134 c
  · exact covered_1_135 c
  · exact covered_1_136 c
  · exact covered_1_137 c
  · exact covered_1_138 c
  · exact covered_1_139 c
  · exact covered_1_140 c
  · exact covered_1_141 c
  · exact covered_1_142 c
  · exact covered_1_143 c
  · exact covered_1_144 c
  · exact covered_1_145 c
  · exact covered_1_146 c
  · exact covered_1_147 c
  · exact covered_1_148 c
  · exact covered_1_149 c
  · exact covered_1_150 c
  · exact covered_1_151 c
  · exact covered_1_152 c
  · exact covered_1_153 c
  · exact covered_1_154 c
  · exact covered_1_155 c
  · exact covered_1_156 c
  · exact covered_1_157 c
  · exact covered_1_158 c
  · exact covered_1_159 c
  · exact covered_1_160 c
  · exact covered_1_161 c
  · exact covered_1_162 c
  · exact covered_1_163 c
  · exact covered_1_164 c
  · exact covered_1_165 c
  · exact covered_1_166 c
  · exact covered_1_167 c
  · exact covered_1_168 c
  · exact covered_1_169 c
  · exact covered_1_170 c
  · exact covered_1_171 c
  · exact covered_1_172 c
  · exact covered_1_173 c
  · exact covered_1_174 c
  · exact covered_1_175 c
  · exact covered_1_176 c
  · exact covered_1_177 c
  · exact covered_1_178 c
  · exact covered_1_179 c
  · exact covered_1_180 c
  · exact covered_1_181 c
  · exact covered_1_182 c
  · exact covered_1_183 c
  · exact covered_1_184 c
  · exact covered_1_185 c
  · exact covered_1_186 c
  · exact covered_1_187 c
  · exact covered_1_188 c
  · exact covered_1_189 c
  · exact covered_1_190 c
  · exact covered_1_191 c
  · exact covered_1_192 c
  · exact covered_1_193 c
  · exact covered_1_194 c
  · exact covered_1_195 c
  · exact covered_1_196 c
  · exact covered_1_197 c
  · exact covered_1_198 c
  · exact covered_1_199 c
  · exact covered_1_200 c
  · exact covered_1_201 c
  · exact covered_1_202 c
  · exact covered_1_203 c
  · exact covered_1_204 c
  · exact covered_1_205 c
  · exact covered_1_206 c
  · exact covered_1_207 c
  · exact covered_1_208 c
  · exact covered_1_209 c
  · exact covered_1_210 c
  · exact covered_1_211 c
  · exact covered_1_212 c
  · exact covered_1_213 c
  · exact covered_1_214 c
  · exact covered_1_215 c
  · exact covered_1_216 c
  · exact covered_1_217 c
  · exact covered_1_218 c
  · exact covered_1_219 c
  · exact covered_1_220 c
  · exact covered_1_221 c
  · exact covered_1_222 c
  · exact covered_1_223 c
  · exact covered_1_224 c
  · exact covered_1_225 c
  · exact covered_1_226 c
  · exact covered_1_227 c
  · exact covered_1_228 c
  · exact covered_1_229 c
  · exact covered_1_230 c
  · exact covered_1_231 c
  · exact covered_1_232 c
  · exact covered_1_233 c
  · exact covered_1_234 c
  · exact covered_1_235 c
  · exact covered_1_236 c
  · exact covered_1_237 c
  · exact covered_1_238 c
  · exact covered_1_239 c
  · exact covered_1_240 c
  · exact covered_1_241 c
  · exact covered_1_242 c
  · exact covered_1_243 c
  · exact covered_1_244 c
  · exact covered_1_245 c
  · exact covered_1_246 c
  · exact covered_1_247 c
  · exact covered_1_248 c
  · exact covered_1_249 c
  · exact covered_1_250 c
  · exact covered_1_251 c
  · exact covered_1_252 c
  · exact covered_1_253 c
  · exact covered_1_254 c
  · exact covered_1_255 c
  · exact covered_1_256 c
  · exact covered_1_257 c
  · exact covered_1_258 c
  · exact covered_1_259 c
  · exact covered_1_260 c
  · exact covered_1_261 c
  · exact covered_1_262 c
  · exact covered_1_263 c
  · exact covered_1_264 c
  · exact covered_1_265 c
  · exact covered_1_266 c
  · exact covered_1_267 c
  · exact covered_1_268 c
  · exact covered_1_269 c
  · exact covered_1_270 c
  · exact covered_1_271 c
  · exact covered_1_272 c
  · exact covered_1_273 c
  · exact covered_1_274 c
  · exact covered_1_275 c
  · exact covered_1_276 c
  · exact covered_1_277 c
  · exact covered_1_278 c
  · exact covered_1_279 c
  · exact covered_1_280 c
  · exact covered_1_281 c
  · exact covered_1_282 c
  · exact covered_1_283 c
  · exact covered_1_284 c
  · exact covered_1_285 c
  · exact covered_1_286 c
  · exact covered_1_287 c
  · exact covered_1_288 c
  · exact covered_1_289 c
  · exact covered_1_290 c
  · exact covered_1_291 c
  · exact covered_1_292 c
  · exact covered_1_293 c
  · exact covered_1_294 c
  · exact covered_1_295 c
  · exact covered_1_296 c
  · exact covered_1_297 c
  · exact covered_1_298 c
  · exact covered_1_299 c
  · exact covered_1_300 c
  · exact covered_1_301 c
  · exact covered_1_302 c
  · exact covered_1_303 c
  · exact covered_1_304 c
  · exact covered_1_305 c
  · exact covered_1_306 c
end Holant.Certificates.AffineEndpoint.BaseCertificate
