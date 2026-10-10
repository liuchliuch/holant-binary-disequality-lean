import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData0016 : Array Nat := #[0,1337,1,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,1,0,0,857,0,0,1,0,1,0,1,0,421,0]
 theorem packetPass0016 : packetCheck 248 false 0 packetData0016=true := by decide +kernel

 def packetData0017 : Array Nat := #[1,0,1,0,1,0,445,0,0,1367,1,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,1,0,0,887,0,0]
 theorem packetPass0017 : packetCheck 249 false 0 packetData0017=true := by decide +kernel

 def packetData0018 : Array Nat := #[0,0,0,1241,1,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,1,0,0,953,445,0,1,0,1,0,1,0]
 theorem packetPass0018 : packetCheck 250 false 0 packetData0018=true := by decide +kernel

 def packetData0019 : Array Nat := #[421,0,1,0,1,0,1,0,0,0,0,1271,1,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,1,0,0,983]
 theorem packetPass0019 : packetCheck 251 false 0 packetData0019=true := by decide +kernel

 def packetData0020 : Array Nat := #[35,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0]
 theorem packetPass0020 : packetCheck 204 true 0 packetData0020=true := by decide +kernel

 def packetData0021 : Array Nat := #[228,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0]
 theorem packetPass0021 : packetCheck 236 true 0 packetData0021=true := by decide +kernel

 def packetData0022 : Array Nat := #[421,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0022 : packetCheck 248 true 0 packetData0022=true := by decide +kernel

 def packetData0023 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0023 : packetCheck 280 true 64 packetData0023=true := by decide +kernel

 def packetData0024 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,252,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0024 : packetCheck 284 true 64 packetData0024=true := by decide +kernel

 def packetData0025 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,445,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0025 : packetCheck 286 true 256 packetData0025=true := by decide +kernel

 def packetData0026 : Array Nat := #[1,1,0,0,0,0,1,1,1,1,0,0,0,0,0,0,1,445,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,1,1,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0]
 theorem packetPass0026 : packetCheck 292 true 64 packetData0026=true := by decide +kernel

 def packetData0027 : Array Nat := #[1,0,1,0,0,1,0,1,1,0,1,0,0,0,0,0,1,0,252,0,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0027 : packetCheck 294 true 256 packetData0027=true := by decide +kernel

 def packetData0028 : Array Nat := #[2,0,0,0,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0028 : packetCheck 298 true 320 packetData0028=true := by decide +kernel

 def packetData0029 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,1,1,749,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,983,1]
 theorem packetPass0029 : packetCheck 304 true 0 packetData0029=true := by decide +kernel

 def packetData0030 : Array Nat := #[2,1,0,2,2,0,1,1037,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1271,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0030 : packetCheck 304 true 64 packetData0030=true := by decide +kernel

 def packetData0031 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1553,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0031 : packetCheck 304 true 128 packetData0031=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
