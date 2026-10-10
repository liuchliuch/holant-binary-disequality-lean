import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddSource
open Holant
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val))
def literal (j : Fin s) : NativeAntiTargetSource.Output H (arity j.val) where
  network:=Network.corolla (H j)
  labels:=Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork.corolla H j
  exact:=Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork.exact_corolla H j
  native:=fun e=>Fin.elim0 e

theorem literal_value (j : Fin s) : (literal H j).network.denote=H j:=Network.denote_corolla _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureOddSource
end
