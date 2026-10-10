import Holant.Proofs.Closure.ProgrammeCompose
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePairedHardGraphs
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareDataCore
import Holant.Proofs.Dichotomy.Native.NativeVertexFieldCodec
import Holant.Proofs.Hardness.GeneralEOPureFamilyAccess

/-! Actual paired EO macros feed the universal finite-family EO theorem.
The macro coefficient field, vertex-generated coefficient field, the existing
fixed presentation, and the final original oracle are connected by executed
length-controlled programmes, with no classification callback. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHard
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace P
export NoIPurePairedHardForm (paired central not_tract)
end P
namespace A
export GeneralEOPureFamilyAccess (arity family source)
end A
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'

abbrev mapped {n : ℕ} (N : NativeAntiTargetSource.Output D.table n):=
  NoIPurePairedHardGraphs.mapped D.K D.table N

theorem mapped_denote {n : ℕ} (N : NativeAntiTargetSource.Output D.table n) :
    (mapped target D N).network.denote=fun z=>(N.network.denote z : AlgebraicComplex) :=
  NoIPurePairedHardGraphs.mapped_denote D.K D.table N

variable {t : ℕ} (row : Fin t→AnySignature AlgebraicComplex)
variable (N : (i : Fin t)→NativeAntiTargetSource.Output D.table (row i).1)
variable (form : ∀i,(fun z=>((N i).network.denote z : AlgebraicComplex))=(row i).2)

abbrev templates:=NoIPurePairedHardGraphs.templates D.K D.table row N
abbrev valid:=NoIPurePairedHardGraphs.valid D.K D.table row N
abbrev table:=A.family (NativeVertexFieldCodec.ambient D.K D.table)
  (templates target D row N) (valid target D row N)

def back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 (A.arity (templates target D row N)))
    (GeneralEOPureFamilyAccess.macroPresentation (NativeVertexFieldCodec.ambient D.K D.table)
      (templates target D row N) (valid target D row N)).encoding
    target.inputEncoding target.outputEncoding
    (GeneralEOPureFamilyAccess.macroValue (NativeVertexFieldCodec.ambient D.K D.table)
      (templates target D row N) (valid target D row N)) target.value :=
  Programme.compose (A.source (NativeVertexFieldCodec.ambient D.K D.table)
    (templates target D row N) (valid target D row N))
    (Programme.compose (NativeVertexFieldCodec.controlled D.K D.F D.table) D.back)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePairedHard
end
