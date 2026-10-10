import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData1056 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1056 : packetCheck 252 true 0 packetData1056=true := by decide +kernel

 def packetData1057 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1057 : packetCheck 253 true 0 packetData1057=true := by decide +kernel

 def packetData1058 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1058 : packetCheck 254 true 0 packetData1058=true := by decide +kernel

 def packetData1059 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1059 : packetCheck 255 true 0 packetData1059=true := by decide +kernel

 def packetData1060 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1060 : packetCheck 256 true 0 packetData1060=true := by decide +kernel

 def packetData1061 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1061 : packetCheck 257 true 0 packetData1061=true := by decide +kernel

 def packetData1062 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1062 : packetCheck 258 true 0 packetData1062=true := by decide +kernel

 def packetData1063 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1063 : packetCheck 259 true 0 packetData1063=true := by decide +kernel

 def packetData1064 : Array Nat := #[0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1064 : packetCheck 260 true 0 packetData1064=true := by decide +kernel

 def packetData1065 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1065 : packetCheck 261 true 0 packetData1065=true := by decide +kernel

 def packetData1066 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1066 : packetCheck 262 true 0 packetData1066=true := by decide +kernel

 def packetData1067 : Array Nat := #[0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1067 : packetCheck 263 true 0 packetData1067=true := by decide +kernel

 def packetData1068 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1068 : packetCheck 264 true 0 packetData1068=true := by decide +kernel

 def packetData1069 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1069 : packetCheck 265 true 0 packetData1069=true := by decide +kernel

 def packetData1070 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1070 : packetCheck 266 true 0 packetData1070=true := by decide +kernel

 def packetData1071 : Array Nat := #[0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1071 : packetCheck 267 true 0 packetData1071=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
