import Holant.Certificates.AffineEndpoint.Retention
import Holant.Certificates.AffineEndpoint.DescriptorChecker
namespace Holant.Certificates.AffineEndpointCounts
open Holant.Certificates.AffineEndpoint IntegerValues
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem retained_witness_ge_ten (s : SupportCatalog.SupportIndex) (c : Nat) (b : Bool)
    (w : Nat) (hw : BaseWitnessCheck s c b w) (hr : BaseRetained s c b) : 10 ≤ w := by
  by_contra h
  have hlt : w < 10 := by omega
  rcases hr with ⟨h0,h1,ho⟩
  by_cases h8 : w < 8
  · simp only [BaseWitnessCheck,dif_pos h8] at hw
    exact hw (ho ⟨w,h8⟩)
  · by_cases he : w = 8
    · simp only [BaseWitnessCheck,dif_neg h8,if_pos he] at hw
      exact h0 hw
    · have he9 : w = 9 := by omega
      simp only [BaseWitnessCheck,dif_neg h8,if_neg he,if_pos he9] at hw
      exact h1 hw

def packetRouteCheck (s : SupportCatalog.SupportIndex) (start : Nat)
    (ws : Array Nat) (ps : List (Nat × Nat)) : Bool :=
  (List.range ws.size).all (fun i => decide (ws.getD i 0 < 10 ∨ (s.val,start+i) ∈ ps))

theorem packet_retained_route (s : SupportCatalog.SupportIndex) (b : Bool) (start : Nat)
    (ws : Array Nat) (ps : List (Nat × Nat))
    (hpass : packetCheck s b start ws = true) (hroute : packetRouteCheck s start ws ps = true)
    (i : Nat) (hi : i < ws.size) (hr : BaseRetained s (start+i) b) :
    (s.val,start+i) ∈ ps := by
  have hw := packetCheck_sound s b start ws hpass i hi
  have hge := retained_witness_ge_ten s (start+i) b _ hw hr
  have hh : ws.getD i 0 < 10 ∨ (s.val,start+i) ∈ ps :=
    of_decide_eq_true (List.all_eq_true.mp hroute i (List.mem_range.mpr hi))
  exact hh.resolve_left (by omega)

end Holant.Certificates.AffineEndpointCounts
