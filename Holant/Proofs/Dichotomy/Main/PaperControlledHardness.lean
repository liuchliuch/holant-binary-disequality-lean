import Holant.Proofs.Algorithms.OriginalForestSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.Target

/-! The engine retains the same controlled counting-hardness predicate as
its target-polymorphic ordinary terminal. Control is forgotten only after
the final native or ordinary oracle and its answer field have been fixed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledHardness
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false

def target {β δ : Type} (eb : Encoding β Bool) (ed : Encoding δ Bool)
    (g : β→δ) : NoIOrdinaryRaw.Target where
  Input:=β
  Output:=δ
  inputEncoding:=eb
  outputEncoding:=ed
  value:=g
abbrev Hard {β δ : Type} (eb : Encoding β Bool) (ed : Encoding δ Bool)
    (g : β→δ) : Prop := (target eb ed g).Hard

variable {β δ γ ε : Type} {eb : Encoding β Bool} {ed : Encoding δ Bool}
variable {ec : Encoding γ Bool} {ee : Encoding ε Bool} {g : β→δ} {h : γ→ε}

theorem forget (hard : Hard eb ed g) :
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard eb ed g :=
  NoIOrdinaryRaw.Target.Hard.witness hard

theorem compose (hard : Hard eb ed g)
    (source : LengthControlledOracleReduction eb ed ec ee g h) : Hard ec ee h :=
  NoIOrdinaryRaw.Target.Hard.compose hard source

def originalTarget {s : ℕ} {a : ℕ→ℕ}
    (G : (i : Fin s)→Signature AlgebraicComplex (a i.val)) : NoIOrdinaryRaw.Target :=
  target (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)
abbrev Original {s : ℕ} {a : ℕ→ℕ}
    (G : (i : Fin s)→Signature AlgebraicComplex (a i.val)) := (originalTarget G).Hard


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlledHardness
end
