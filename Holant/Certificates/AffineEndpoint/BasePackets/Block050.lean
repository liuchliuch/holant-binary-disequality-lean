import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData0800 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0800 : packetCheck 306 false 15936 packetData0800=true := by decide +kernel

 def packetData0801 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0801 : packetCheck 306 false 16000 packetData0801=true := by decide +kernel

 def packetData0802 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0802 : packetCheck 306 false 16064 packetData0802=true := by decide +kernel

 def packetData0803 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0803 : packetCheck 306 false 16128 packetData0803=true := by decide +kernel

 def packetData0804 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0804 : packetCheck 306 false 16192 packetData0804=true := by decide +kernel

 def packetData0805 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0805 : packetCheck 306 false 16256 packetData0805=true := by decide +kernel

 def packetData0806 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0806 : packetCheck 306 false 16320 packetData0806=true := by decide +kernel

 def packetData0807 : Array Nat := #[0]
 theorem packetPass0807 : packetCheck 0 true 0 packetData0807=true := by decide +kernel

 def packetData0808 : Array Nat := #[0]
 theorem packetPass0808 : packetCheck 1 true 0 packetData0808=true := by decide +kernel

 def packetData0809 : Array Nat := #[0]
 theorem packetPass0809 : packetCheck 2 true 0 packetData0809=true := by decide +kernel

 def packetData0810 : Array Nat := #[0]
 theorem packetPass0810 : packetCheck 3 true 0 packetData0810=true := by decide +kernel

 def packetData0811 : Array Nat := #[0]
 theorem packetPass0811 : packetCheck 4 true 0 packetData0811=true := by decide +kernel

 def packetData0812 : Array Nat := #[0]
 theorem packetPass0812 : packetCheck 5 true 0 packetData0812=true := by decide +kernel

 def packetData0813 : Array Nat := #[0]
 theorem packetPass0813 : packetCheck 6 true 0 packetData0813=true := by decide +kernel

 def packetData0814 : Array Nat := #[0]
 theorem packetPass0814 : packetCheck 7 true 0 packetData0814=true := by decide +kernel

 def packetData0815 : Array Nat := #[0]
 theorem packetPass0815 : packetCheck 8 true 0 packetData0815=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
