import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData1024 : Array Nat := #[1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1024 : packetCheck 218 true 0 packetData1024=true := by decide +kernel

 def packetData1025 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1025 : packetCheck 219 true 0 packetData1025=true := by decide +kernel

 def packetData1026 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1026 : packetCheck 220 true 0 packetData1026=true := by decide +kernel

 def packetData1027 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1027 : packetCheck 221 true 0 packetData1027=true := by decide +kernel

 def packetData1028 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]
 theorem packetPass1028 : packetCheck 222 true 0 packetData1028=true := by decide +kernel

 def packetData1029 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]
 theorem packetPass1029 : packetCheck 223 true 0 packetData1029=true := by decide +kernel

 def packetData1030 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1030 : packetCheck 224 true 0 packetData1030=true := by decide +kernel

 def packetData1031 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1031 : packetCheck 225 true 0 packetData1031=true := by decide +kernel

 def packetData1032 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1032 : packetCheck 226 true 0 packetData1032=true := by decide +kernel

 def packetData1033 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1033 : packetCheck 227 true 0 packetData1033=true := by decide +kernel

 def packetData1034 : Array Nat := #[1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0]
 theorem packetPass1034 : packetCheck 228 true 0 packetData1034=true := by decide +kernel

 def packetData1035 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1035 : packetCheck 229 true 0 packetData1035=true := by decide +kernel

 def packetData1036 : Array Nat := #[1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0]
 theorem packetPass1036 : packetCheck 230 true 0 packetData1036=true := by decide +kernel

 def packetData1037 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1037 : packetCheck 231 true 0 packetData1037=true := by decide +kernel

 def packetData1038 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1038 : packetCheck 232 true 0 packetData1038=true := by decide +kernel

 def packetData1039 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass1039 : packetCheck 233 true 0 packetData1039=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
