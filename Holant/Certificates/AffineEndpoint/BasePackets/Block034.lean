import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData0544 : Array Nat := #[2,1,0,2,2,0,1,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,2,0,0,0,0,0,0,0,0,0,0,1,0,2,0,0,0]
 theorem packetPass0544 : packetCheck 305 false 64 packetData0544=true := by decide +kernel

 def packetData0545 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,0,0,0,0,3,0,1,0,0,1,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0]
 theorem packetPass0545 : packetCheck 305 false 128 packetData0545=true := by decide +kernel

 def packetData0546 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,2,0,1,0,3,0,0,2,2,0,0,2,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0]
 theorem packetPass0546 : packetCheck 305 false 192 packetData0546=true := by decide +kernel

 def packetData0547 : Array Nat := #[3,0,1,2,2,1,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,2,1,0,0]
 theorem packetPass0547 : packetCheck 305 false 256 packetData0547=true := by decide +kernel

 def packetData0548 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0]
 theorem packetPass0548 : packetCheck 305 false 320 packetData0548=true := by decide +kernel

 def packetData0549 : Array Nat := #[0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,3,0,0,0,0,0,0,0,0,0,1,0,0,2,0,0,0,2,0,0,2,2,0,0,3,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0549 : packetCheck 305 false 384 packetData0549=true := by decide +kernel

 def packetData0550 : Array Nat := #[0,0,0,0,0,0,0,0,0,1,0,2,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0550 : packetCheck 305 false 448 packetData0550=true := by decide +kernel

 def packetData0551 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0551 : packetCheck 306 false 0 packetData0551=true := by decide +kernel

 def packetData0552 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0552 : packetCheck 306 false 64 packetData0552=true := by decide +kernel

 def packetData0553 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0553 : packetCheck 306 false 128 packetData0553=true := by decide +kernel

 def packetData0554 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0554 : packetCheck 306 false 192 packetData0554=true := by decide +kernel

 def packetData0555 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0555 : packetCheck 306 false 256 packetData0555=true := by decide +kernel

 def packetData0556 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0556 : packetCheck 306 false 320 packetData0556=true := by decide +kernel

 def packetData0557 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0557 : packetCheck 306 false 384 packetData0557=true := by decide +kernel

 def packetData0558 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0558 : packetCheck 306 false 448 packetData0558=true := by decide +kernel

 def packetData0559 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0559 : packetCheck 306 false 512 packetData0559=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
