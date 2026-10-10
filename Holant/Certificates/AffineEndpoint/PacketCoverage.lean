import Holant.Certificates.AffineEndpoint.DescriptorChecker
namespace Holant.Certificates.AffineEndpoint.BaseCertificate
open SupportCatalog
set_option backward.isDefEq.respectTransparency false
 theorem packet_coverage (s : SupportIndex) (b : Bool) (N P : Nat)
    (hN : N=P*64) (ws : Fin P → Array Nat)
    (hsize : ∀p,(ws p).size=64)
    (hpass : ∀p,packetCheck s b (p.val*64) (ws p)=true)
    (c : Fin N) : ∃w,BaseWitnessCheck s c.val b w := by
  let p : Fin P := ⟨c.val/64,by have h:=c.isLt; omega⟩
  let i := c.val%64
  have hi : i<(ws p).size := by rw [hsize]; exact Nat.mod_lt _ (by decide)
  have h := packetCheck_sound s b (p.val*64) (ws p) (hpass p) i hi
  have he : p.val*64+i=c.val := by dsimp [p,i]; omega
  rw [he] at h
  exact ⟨(ws p).getD i 0,h⟩

end Holant.Certificates.AffineEndpoint.BaseCertificate
