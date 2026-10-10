import Holant.Proofs.CountingMachines.OracleControl.Fees
import Holant.Proofs.CountingMachines.AnswerDecoder.Storage

/-! Faithful coded storage of the actual oracle configuration. Only the finite
shape is shared with the ordinary-machine serializer. The dummy halt table below
is never executed or substituted for the oracle program. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
open Turing Computability Holant.Complexity BinaryCompose
noncomputable section

/-- A type-level configuration-shape adapter, solely for serialization. -/
def serializationShape (m : OracleMachine) : Machine where
  K := m.K
  input := m.inputStack
  output := m.outputStack
  Label := m.Λ
  main := m.main
  State := m.σ
  initial := m.initialState
  program _ := .halt

def configurationWord (m : OracleMachine) (c : m.Cfg) : List Bool :=
  AnswerDecoder.Storage.configurationWord (serializationShape m) c

theorem configurationWord_injective (m : OracleMachine) :
    Function.Injective (configurationWord m) :=
  AnswerDecoder.Storage.configurationWord_injective (serializationShape m)

theorem configurationWord_parses (m : OracleMachine) (c : m.Cfg) :
    AnswerDecoder.Storage.dataEncoding.decode (configurationWord m c) =
      some (AnswerDecoder.Storage.configurationData (serializationShape m) c) :=
  AnswerDecoder.Storage.configurationWord_parses (serializationShape m) c

theorem configurationWord_length (m : OracleMachine) (c : m.Cfg) :
    (configurationWord m c).length ≤ 2 * stackSize c.stk +
      AnswerDecoder.Storage.controlOverhead (serializationShape m) :=
  AnswerDecoder.Storage.configurationWord_length (serializationShape m) c

variable {α β γ δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}

def codedStoragePolynomial (r : LengthControlledOracleReduction ea eb ec ed f g) :
    Polynomial ℕ :=
  2 * r.sourceOutputPolynomial + Polynomial.C
    (AnswerDecoder.Storage.controlOverhead (serializationShape r.reduction.machine))

theorem coded_storage_le (r : LengthControlledOracleReduction ea eb ec ed f g)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ec ed g oracle)
    (x : α) (t : ℕ) (ht : t ≤ r.reduction.time.eval (ea.encode x).length)
    (c : r.reduction.machine.Cfg)
    (hr : r.reduction.machine.run oracle (ea.encode x) t = some c) :
    (configurationWord r.reduction.machine c).length ≤
      (codedStoragePolynomial r).eval (ea.encode x).length := by
  have hc := configurationWord_length r.reduction.machine c
  have hs := storage_le r oracle ho x t ht c hr
  simp only [codedStoragePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_C]
  omega

end
end Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
