import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData1120 : Array Nat := #[0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,2,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2]
 theorem packetPass1120 : packetCheck 281 true 64 packetData1120=true := by decide +kernel

 def packetData1121 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1121 : packetCheck 281 true 128 packetData1121=true := by decide +kernel

 def packetData1122 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0]
 theorem packetPass1122 : packetCheck 281 true 192 packetData1122=true := by decide +kernel

 def packetData1123 : Array Nat := #[2,8,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0]
 theorem packetPass1123 : packetCheck 281 true 256 packetData1123=true := by decide +kernel

 def packetData1124 : Array Nat := #[2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0]
 theorem packetPass1124 : packetCheck 281 true 320 packetData1124=true := by decide +kernel

 def packetData1125 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1125 : packetCheck 281 true 384 packetData1125=true := by decide +kernel

 def packetData1126 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1126 : packetCheck 281 true 448 packetData1126=true := by decide +kernel

 def packetData1127 : Array Nat := #[0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1127 : packetCheck 282 true 0 packetData1127=true := by decide +kernel

 def packetData1128 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1128 : packetCheck 282 true 64 packetData1128=true := by decide +kernel

 def packetData1129 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1129 : packetCheck 282 true 128 packetData1129=true := by decide +kernel

 def packetData1130 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1130 : packetCheck 282 true 192 packetData1130=true := by decide +kernel

 def packetData1131 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1131 : packetCheck 282 true 256 packetData1131=true := by decide +kernel

 def packetData1132 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1132 : packetCheck 282 true 320 packetData1132=true := by decide +kernel

 def packetData1133 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1133 : packetCheck 282 true 384 packetData1133=true := by decide +kernel

 def packetData1134 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1134 : packetCheck 282 true 448 packetData1134=true := by decide +kernel

 def packetData1135 : Array Nat := #[0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1135 : packetCheck 283 true 0 packetData1135=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
