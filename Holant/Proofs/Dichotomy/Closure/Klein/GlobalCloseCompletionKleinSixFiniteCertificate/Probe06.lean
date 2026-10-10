import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixLinearPacked
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixFiniteCertificate.Probe06
open GlobalCloseCompletionKleinSixFiniteData
namespace L
export GlobalCloseCompletionKleinSixLinearPacked (accepted)
end L
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def blockIndex (h : Fin 6) (b : Fin 8) : Fin 48 := ⟨8*h.val+b.val,by omega⟩

theorem block0 : ∀b : Fin 8,∀c : Fin 48,∀s : Fin 8,
    L.accepted 6 (blockIndex 0 b) c s=true→allowed 6 (blockIndex 0 b) c := by
  unfold allowed
  decide +kernel

theorem block1 : ∀b : Fin 8,∀c : Fin 48,∀s : Fin 8,
    L.accepted 6 (blockIndex 1 b) c s=true→allowed 6 (blockIndex 1 b) c := by
  unfold allowed
  decide +kernel

theorem block2 : ∀b : Fin 8,∀c : Fin 48,∀s : Fin 8,
    L.accepted 6 (blockIndex 2 b) c s=true→allowed 6 (blockIndex 2 b) c := by
  unfold allowed
  decide +kernel

theorem block3 : ∀b : Fin 8,∀c : Fin 48,∀s : Fin 8,
    L.accepted 6 (blockIndex 3 b) c s=true→allowed 6 (blockIndex 3 b) c := by
  unfold allowed
  decide +kernel

theorem block4 : ∀b : Fin 8,∀c : Fin 48,∀s : Fin 8,
    L.accepted 6 (blockIndex 4 b) c s=true→allowed 6 (blockIndex 4 b) c := by
  unfold allowed
  decide +kernel

theorem block5 : ∀b : Fin 8,∀c : Fin 48,∀s : Fin 8,
    L.accepted 6 (blockIndex 5 b) c s=true→allowed 6 (blockIndex 5 b) c := by
  unfold allowed
  decide +kernel

theorem blocks (h : Fin 6) : ∀b : Fin 8,∀c : Fin 48,∀s : Fin 8,
    L.accepted 6 (blockIndex h b) c s=true→allowed 6 (blockIndex h b) c := by
  fin_cases h
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5

theorem certificate : ∀b c : Fin 48,∀s : Fin 8,L.accepted 6 b c s=true→allowed 6 b c := by
  intro b c s
  let h : Fin 6 := ⟨b.val/8,by omega⟩
  let k : Fin 8 := ⟨b.val%8,Nat.mod_lt _ (by decide)⟩
  have equal : blockIndex h k=b := by apply Fin.ext;dsimp [blockIndex,h,k];omega
  rw [←equal]
  exact blocks h k c s

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixFiniteCertificate.Probe06
