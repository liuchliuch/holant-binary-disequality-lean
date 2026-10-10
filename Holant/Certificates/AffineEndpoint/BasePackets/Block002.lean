import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData0032 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1973,2,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0032 : packetCheck 304 true 192 packetData0032=true := by decide +kernel

 def packetData0033 : Array Nat := #[3,0,1,2,2,1,0,1091,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0033 : packetCheck 304 true 256 packetData0033=true := by decide +kernel

 def packetData0034 : Array Nat := #[0,0,0,0,0,0,0,0,1,0,1,0,0,1919,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,2075,2,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0034 : packetCheck 304 true 384 packetData0034=true := by decide +kernel

 def packetData0035 : Array Nat := #[0,0,0,0,0,0,0,611,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0035 : packetCheck 305 true 0 packetData0035=true := by decide +kernel

 def packetData0036 : Array Nat := #[0,2,1,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,3,0,0,0,0,0,2,0,2,0,0,0,0,0,2,0,0,3,0,0,0,0,1,0,0,0,0,0,0,0,0,0,2,1,0,0,0,0,1133]
 theorem packetPass0036 : packetCheck 306 true 2688 packetData0036=true := by decide +kernel

 def packetData0037 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1685,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1841,0,0,0,0,0,1337,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0037 : packetCheck 306 true 5440 packetData0037=true := by decide +kernel

 def packetData0038 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1367,0,0,0,0]
 theorem packetPass0038 : packetCheck 306 true 6848 packetData0038=true := by decide +kernel

 def packetData0039 : Array Nat := #[0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1937,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1]
 theorem packetPass0039 : packetCheck 306 true 7040 packetData0039=true := by decide +kernel

 def packetData0040 : Array Nat := #[0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,2069,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,2]
 theorem packetPass0040 : packetCheck 306 true 7808 packetData0040=true := by decide +kernel

 def packetData0041 : Array Nat := #[0,2,0,0,1,0,0,2,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,2,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,2,0,0,1,0,0,995]
 theorem packetPass0041 : packetCheck 306 true 8832 packetData0041=true := by decide +kernel

 def packetData0042 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1823,0,0]
 theorem packetPass0042 : packetCheck 306 true 9920 packetData0042=true := by decide +kernel

 def packetData0043 : Array Nat := #[0,0,0,0,1,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1241,0,0,0,0,1,0,0,1]
 theorem packetPass0043 : packetCheck 306 true 10112 packetData0043=true := by decide +kernel

 def packetData0044 : Array Nat := #[0,0,1,0,1,0,0,1,0,0,0,0,1,0,0,1,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,1,0,1,0,0,707]
 theorem packetPass0044 : packetCheck 306 true 10368 packetData0044=true := by decide +kernel

 def packetData0045 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1691,0]
 theorem packetPass0045 : packetCheck 306 true 10688 packetData0045=true := by decide +kernel

 def packetData0046 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,653]
 theorem packetPass0046 : packetCheck 306 true 10752 packetData0046=true := by decide +kernel

 def packetData0047 : Array Nat := #[0,2,1,0,1,0,0,0,0,0,0,0,421,0,0,0,0,0,228,0,0,0,0,0,0,0,0,0,0,0,0,0,0,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,2,0]
 theorem packetPass0047 : packetCheck 306 true 10880 packetData0047=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
