import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData1040 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1040 : packetCheck 234 true 0 packetData1040=true := by decide +kernel

 def packetData1041 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1041 : packetCheck 235 true 0 packetData1041=true := by decide +kernel

 def packetData1042 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1042 : packetCheck 237 true 0 packetData1042=true := by decide +kernel

 def packetData1043 : Array Nat := #[1,0,0,0,0,0,0,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1,0,0,0,0,0,0,1]
 theorem packetPass1043 : packetCheck 238 true 0 packetData1043=true := by decide +kernel

 def packetData1044 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,8,0,1,0,0,0,0,0,0,0,0,0]
 theorem packetPass1044 : packetCheck 239 true 0 packetData1044=true := by decide +kernel

 def packetData1045 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1045 : packetCheck 240 true 0 packetData1045=true := by decide +kernel

 def packetData1046 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1046 : packetCheck 241 true 0 packetData1046=true := by decide +kernel

 def packetData1047 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1047 : packetCheck 242 true 0 packetData1047=true := by decide +kernel

 def packetData1048 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1048 : packetCheck 243 true 0 packetData1048=true := by decide +kernel

 def packetData1049 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1049 : packetCheck 244 true 0 packetData1049=true := by decide +kernel

 def packetData1050 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1050 : packetCheck 245 true 0 packetData1050=true := by decide +kernel

 def packetData1051 : Array Nat := #[0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0]
 theorem packetPass1051 : packetCheck 246 true 0 packetData1051=true := by decide +kernel

 def packetData1052 : Array Nat := #[0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0]
 theorem packetPass1052 : packetCheck 247 true 0 packetData1052=true := by decide +kernel

 def packetData1053 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1053 : packetCheck 249 true 0 packetData1053=true := by decide +kernel

 def packetData1054 : Array Nat := #[1,0,1,0,1,0,1,0,0,0,0,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1]
 theorem packetPass1054 : packetCheck 250 true 0 packetData1054=true := by decide +kernel

 def packetData1055 : Array Nat := #[0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,1,0,0,0]
 theorem packetPass1055 : packetCheck 251 true 0 packetData1055=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
