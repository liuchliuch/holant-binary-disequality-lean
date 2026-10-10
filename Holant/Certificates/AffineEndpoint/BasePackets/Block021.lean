import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData0336 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0336 : packetCheck 279 false 64 packetData0336=true := by decide +kernel

 def packetData0337 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0337 : packetCheck 279 false 128 packetData0337=true := by decide +kernel

 def packetData0338 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0338 : packetCheck 279 false 192 packetData0338=true := by decide +kernel

 def packetData0339 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0339 : packetCheck 279 false 256 packetData0339=true := by decide +kernel

 def packetData0340 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0340 : packetCheck 279 false 320 packetData0340=true := by decide +kernel

 def packetData0341 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0341 : packetCheck 279 false 384 packetData0341=true := by decide +kernel

 def packetData0342 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0342 : packetCheck 279 false 448 packetData0342=true := by decide +kernel

 def packetData0343 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0343 : packetCheck 280 false 0 packetData0343=true := by decide +kernel

 def packetData0344 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0344 : packetCheck 280 false 64 packetData0344=true := by decide +kernel

 def packetData0345 : Array Nat := #[2,2,0,0,0,0,2,2,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,2,2,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0]
 theorem packetPass0345 : packetCheck 280 false 128 packetData0345=true := by decide +kernel

 def packetData0346 : Array Nat := #[2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,2,2,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,0,0,2,2,0,0,0,0,2,2]
 theorem packetPass0346 : packetCheck 280 false 192 packetData0346=true := by decide +kernel

 def packetData0347 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0347 : packetCheck 280 false 256 packetData0347=true := by decide +kernel

 def packetData0348 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0348 : packetCheck 280 false 320 packetData0348=true := by decide +kernel

 def packetData0349 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0]
 theorem packetPass0349 : packetCheck 280 false 384 packetData0349=true := by decide +kernel

 def packetData0350 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0]
 theorem packetPass0350 : packetCheck 280 false 448 packetData0350=true := by decide +kernel

 def packetData0351 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0]
 theorem packetPass0351 : packetCheck 281 false 0 packetData0351=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
