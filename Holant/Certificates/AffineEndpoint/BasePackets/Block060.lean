import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData0960 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]
 theorem packetPass0960 : packetCheck 153 true 0 packetData0960=true := by decide +kernel

 def packetData0961 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0961 : packetCheck 154 true 0 packetData0961=true := by decide +kernel

 def packetData0962 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0]
 theorem packetPass0962 : packetCheck 155 true 0 packetData0962=true := by decide +kernel

 def packetData0963 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0963 : packetCheck 156 true 0 packetData0963=true := by decide +kernel

 def packetData0964 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0964 : packetCheck 157 true 0 packetData0964=true := by decide +kernel

 def packetData0965 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,2,0,2,0,0,0,0,0,0,0,0,0]
 theorem packetPass0965 : packetCheck 158 true 0 packetData0965=true := by decide +kernel

 def packetData0966 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,2,0,2,0,2,0,0,0,0,0,0,0,0,0]
 theorem packetPass0966 : packetCheck 159 true 0 packetData0966=true := by decide +kernel

 def packetData0967 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0967 : packetCheck 160 true 0 packetData0967=true := by decide +kernel

 def packetData0968 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0968 : packetCheck 161 true 0 packetData0968=true := by decide +kernel

 def packetData0969 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0969 : packetCheck 162 true 0 packetData0969=true := by decide +kernel

 def packetData0970 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0970 : packetCheck 163 true 0 packetData0970=true := by decide +kernel

 def packetData0971 : Array Nat := #[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0971 : packetCheck 164 true 0 packetData0971=true := by decide +kernel

 def packetData0972 : Array Nat := #[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0972 : packetCheck 165 true 0 packetData0972=true := by decide +kernel

 def packetData0973 : Array Nat := #[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0973 : packetCheck 166 true 0 packetData0973=true := by decide +kernel

 def packetData0974 : Array Nat := #[0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0974 : packetCheck 167 true 0 packetData0974=true := by decide +kernel

 def packetData0975 : Array Nat := #[1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0975 : packetCheck 168 true 0 packetData0975=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
