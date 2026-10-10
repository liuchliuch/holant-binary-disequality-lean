import Holant.Certificates.AffineEndpoint.DescriptorChecker
/-! Bounded kernel-checked coefficient packets. Each witness is checked against
its actual source chart and phase code; candidate generation supplies no proof. -/
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
 def packetData0048 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1589,0]
 theorem packetPass0048 : packetCheck 306 true 11072 packetData0048=true := by decide +kernel

 def packetData0049 : Array Nat := #[0,0,0,0,1,0,0,1,0,0,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,953,0,0,0,0,1,0,0,1]
 theorem packetPass0049 : packetCheck 306 true 11648 packetData0049=true := by decide +kernel

 def packetData0050 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1457,0,0]
 theorem packetPass0050 : packetCheck 306 true 11840 packetData0050=true := by decide +kernel

 def packetData0051 : Array Nat := #[0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1979,0,2,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,2]
 theorem packetPass0051 : packetCheck 306 true 13952 packetData0051=true := by decide +kernel

 def packetData0052 : Array Nat := #[0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1535,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1]
 theorem packetPass0052 : packetCheck 306 true 14720 packetData0052=true := by decide +kernel

 def packetData0053 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,887,0,0,0,0]
 theorem packetPass0053 : packetCheck 306 true 14912 packetData0053=true := by decide +kernel

 def packetData0054 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1595,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1439,0,0,0,0,0,857,0,0,0,0,0,0,0,0,0,0,0,0]
 theorem packetPass0054 : packetCheck 306 true 16320 packetData0054=true := by decide +kernel

 def packetData0055 : Array Nat := #[0]
 theorem packetPass0055 : packetCheck 0 false 0 packetData0055=true := by decide +kernel

 def packetData0056 : Array Nat := #[0]
 theorem packetPass0056 : packetCheck 1 false 0 packetData0056=true := by decide +kernel

 def packetData0057 : Array Nat := #[0]
 theorem packetPass0057 : packetCheck 2 false 0 packetData0057=true := by decide +kernel

 def packetData0058 : Array Nat := #[0]
 theorem packetPass0058 : packetCheck 3 false 0 packetData0058=true := by decide +kernel

 def packetData0059 : Array Nat := #[0]
 theorem packetPass0059 : packetCheck 4 false 0 packetData0059=true := by decide +kernel

 def packetData0060 : Array Nat := #[0]
 theorem packetPass0060 : packetCheck 5 false 0 packetData0060=true := by decide +kernel

 def packetData0061 : Array Nat := #[0]
 theorem packetPass0061 : packetCheck 6 false 0 packetData0061=true := by decide +kernel

 def packetData0062 : Array Nat := #[0]
 theorem packetPass0062 : packetCheck 7 false 0 packetData0062=true := by decide +kernel

 def packetData0063 : Array Nat := #[0]
 theorem packetPass0063 : packetCheck 8 false 0 packetData0063=true := by decide +kernel

end Holant.Certificates.AffineEndpoint.BaseCertificate
