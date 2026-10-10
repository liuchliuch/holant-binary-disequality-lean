import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! The fixed two-row semantic palette used by every positive finite mixer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalPair
open Holant

def arity (n m i : ℕ) : ℕ := if i=0 then n else m

def table {K : Type} {n m : ℕ} (f : Signature K n) (g : Signature K m)
    (i : Fin 2) : Signature K (arity n m i.val) :=
  match i with
  | ⟨0,_⟩=>f
  | ⟨1,_⟩=>g
  | ⟨j+2,h⟩=>False.elim (by omega)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversalPair
end
