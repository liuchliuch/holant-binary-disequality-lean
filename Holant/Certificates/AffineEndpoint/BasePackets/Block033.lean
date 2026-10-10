import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData0528 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0528 : packetCheck 303 false 64 packetData0528=true := by decide +kernel

 def packetData0529 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0529 : packetCheck 303 false 128 packetData0529=true := by decide +kernel

 def packetData0530 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0530 : packetCheck 303 false 192 packetData0530=true := by decide +kernel

 def packetData0531 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0531 : packetCheck 303 false 256 packetData0531=true := by decide +kernel

 def packetData0532 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0532 : packetCheck 303 false 320 packetData0532=true := by decide +kernel

 def packetData0533 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0533 : packetCheck 303 false 384 packetData0533=true := by decide +kernel

 def packetData0534 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0534 : packetCheck 303 false 448 packetData0534=true := by decide +kernel

 def packetData0535 : Array Nat := #[0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,2,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0535 : packetCheck 304 false 0 packetData0535=true := by decide +kernel

 def packetData0536 : Array Nat := #[0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0,0,2,2,0,0,3,0,1,0,0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,3,0,0,0,0,0,0,0,0]
 theorem packetPass0536 : packetCheck 304 false 64 packetData0536=true := by decide +kernel

 def packetData0537 : Array Nat := #[3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0537 : packetCheck 304 false 128 packetData0537=true := by decide +kernel

 def packetData0538 : Array Nat := #[0,0,0,0,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,2,2,1,0,3]
 theorem packetPass0538 : packetCheck 304 false 192 packetData0538=true := by decide +kernel

 def packetData0539 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,3,0,0,2,2,0,0,2,0,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0]
 theorem packetPass0539 : packetCheck 304 false 256 packetData0539=true := by decide +kernel

 def packetData0540 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,3,0,1,0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,0,0,0,0]
 theorem packetPass0540 : packetCheck 304 false 320 packetData0540=true := by decide +kernel

 def packetData0541 : Array Nat := #[0,0,1,0,2,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,0,2,2,0,1,2]
 theorem packetPass0541 : packetCheck 304 false 384 packetData0541=true := by decide +kernel

 def packetData0542 : Array Nat := #[2,1,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0542 : packetCheck 304 false 448 packetData0542=true := by decide +kernel

 def packetData0543 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,1,0,0,0,0,0,0,0,0,0,0,2,1,0,0,0,0,1,1]
 theorem packetPass0543 : packetCheck 305 false 0 packetData0543=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
