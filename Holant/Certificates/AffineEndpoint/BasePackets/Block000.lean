import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData0000 : Array Nat := #[0,0,611,0]
 theorem packetPass0000 : packetCheck 128 false 0 packetData0000=true := by decide +kernel

 def packetData0001 : Array Nat := #[0,0,0,653]
 theorem packetPass0001 : packetCheck 129 false 0 packetData0001=true := by decide +kernel

 def packetData0002 : Array Nat := #[0,0,0,707]
 theorem packetPass0002 : packetCheck 130 false 0 packetData0002=true := by decide +kernel

 def packetData0003 : Array Nat := #[749,0,0,0]
 theorem packetPass0003 : packetCheck 131 false 0 packetData0003=true := by decide +kernel

 def packetData0004 : Array Nat := #[0,0,0,995]
 theorem packetPass0004 : packetCheck 132 false 0 packetData0004=true := by decide +kernel

 def packetData0005 : Array Nat := #[1037,0,0,0]
 theorem packetPass0005 : packetCheck 133 false 0 packetData0005=true := by decide +kernel

 def packetData0006 : Array Nat := #[1091,0,0,0]
 theorem packetPass0006 : packetCheck 134 false 0 packetData0006=true := by decide +kernel

 def packetData0007 : Array Nat := #[0,1133,0,0]
 theorem packetPass0007 : packetCheck 135 false 0 packetData0007=true := by decide +kernel

 def packetData0008 : Array Nat := #[0,1685,0,0,0,0,2,0,2,0,8,0,2,0,2,0,0,0,0,0,0,1595,2,0,0,0,0,0,0,0,35,0]
 theorem packetPass0008 : packetCheck 204 false 0 packetData0008=true := by decide +kernel

 def packetData0009 : Array Nat := #[2,0,0,1691,0,0,0,0,2,0,2,0,8,0,2,0,2,0,0,0,0,0,0,1589,59,0,0,0,0,0,0,0]
 theorem packetPass0009 : packetCheck 205 false 0 packetData0009=true := by decide +kernel

 def packetData0010 : Array Nat := #[0,0,0,0,0,0,59,0,0,2069,0,0,0,0,2,0,2,0,8,0,2,0,2,0,0,0,0,0,0,1979,2,0]
 theorem packetPass0010 : packetCheck 206 false 0 packetData0010=true := by decide +kernel

 def packetData0011 : Array Nat := #[35,0,0,0,0,0,0,0,2,0,0,2075,0,0,0,0,2,0,2,0,8,0,2,0,2,0,0,0,0,0,0,1973]
 theorem packetPass0011 : packetCheck 207 false 0 packetData0011=true := by decide +kernel

 def packetData0012 : Array Nat := #[0,1841,0,0,0,0,1,0,1,0,8,0,1,0,1,0,0,0,0,0,0,1439,1,0,0,0,0,0,0,0,228,0]
 theorem packetPass0012 : packetCheck 236 false 0 packetData0012=true := by decide +kernel

 def packetData0013 : Array Nat := #[1,0,0,1823,0,0,0,0,1,0,1,0,8,0,1,0,1,0,0,0,0,0,0,1457,252,0,0,0,0,0,0,0]
 theorem packetPass0013 : packetCheck 237 false 0 packetData0013=true := by decide +kernel

 def packetData0014 : Array Nat := #[0,0,0,0,0,0,252,0,0,1937,0,0,0,0,1,0,1,0,8,0,1,0,1,0,0,0,0,0,0,1535,1,0]
 theorem packetPass0014 : packetCheck 238 false 0 packetData0014=true := by decide +kernel

 def packetData0015 : Array Nat := #[228,0,0,0,0,0,0,0,1,0,0,1919,0,0,0,0,1,0,1,0,8,0,1,0,1,0,0,0,0,0,0,1553]
 theorem packetPass0015 : packetCheck 239 false 0 packetData0015=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
