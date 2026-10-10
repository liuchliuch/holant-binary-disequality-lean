import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityData

/-! Encode the actual natural signed counts without discarding multiplicity. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityEncoding
open NoXReciprocalRankThreeParityData
namespace P
export OrdinaryNegativeSparseRankThreeParity (pattern)
end P
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

theorem bit_pattern (q : Fin 7→Bool) (j : Fin 7) : bit (P.pattern q) j=q j := by
  revert q j
  decide

def encode (v : Fin 7→ℕ) : Fin 128 := P.pattern (fun i=>decide (v i%2=1))

theorem count_mod (v : Fin 7→ℕ) (j : Fin 7) : v j%2=if bit (encode v) j then 1 else 0 := by
  rw [encode,bit_pattern]
  have hlt:=Nat.mod_lt (v j) (by decide : 0<2)
  split_ifs with h <;> simp_all <;> omega

theorem all_bits : ∀j : Fin 7,bit 127 j=true := by decide

theorem complementary (p n : Fin 128) (h:n.val=127-p.val) : ∀j : Fin 7,bit p j= !(bit n j) := by
  revert p n
  decide


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityEncoding
