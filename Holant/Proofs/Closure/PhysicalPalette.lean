import Holant.Proofs.Closure.PhysicalCosts

/-! Reusable exact-instance gates for each actual palette's returned machines,
including the frozen original-G byte encoding and actual total live storage. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.Palette
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness.FrozenFactorNormalization
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

theorem toOriginal_prefix_costs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) oracle)
    (x : ExactSignatureTables.Input P.count 1 P.arity) (t : ℕ)
    (ht : t ≤ P.toOriginal.controlled.reduction.time.eval
      ((RawClosedNetwork.validatedEncoding P.count 1 P.arity).encode x).length) :
    let bytes := (RawClosedNetwork.validatedEncoding P.count 1 P.arity).encode x
    OracleBatch.primitiveCount P.toOriginal.controlled.reduction.machine oracle
      (P.toOriginal.controlled.reduction.machine.init bytes) t ≤
        P.toOriginal.primitiveBound.eval bytes.length ∧
    (OracleBatch.queryTrace P.toOriginal.controlled.reduction.machine oracle
      (P.toOriginal.controlled.reduction.machine.init bytes) t |>.map List.length).sum +
    (OracleBatch.queryTrace P.toOriginal.controlled.reduction.machine oracle
      (P.toOriginal.controlled.reduction.machine.init bytes) t |>.map (fun q => (oracle q).length)).sum ≤
        P.toOriginal.transcriptBitBound.eval bytes.length :=
  ⟨P.toOriginal.primitives oracle ho x t ht, P.toOriginal.transcriptBits oracle ho x t ht⟩

theorem fromOriginal_prefix_costs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding P.count 1 P.arity)
      (OI.presentation G).encoding (OriginalLCodec.value P.table) oracle)
    (x : EdgeSubdivision.WireEquivalence.Input s a) (t : ℕ)
    (ht : t ≤ P.fromOriginal.controlled.reduction.time.eval
      ((OriginalForestSource.inputEncoding (s:=s) (arity:=a)).encode x).length) :
    let bytes := (OriginalForestSource.inputEncoding (s:=s) (arity:=a)).encode x
    OracleBatch.primitiveCount P.fromOriginal.controlled.reduction.machine oracle
      (P.fromOriginal.controlled.reduction.machine.init bytes) t ≤
        P.fromOriginal.primitiveBound.eval bytes.length ∧
    (OracleBatch.queryTrace P.fromOriginal.controlled.reduction.machine oracle
      (P.fromOriginal.controlled.reduction.machine.init bytes) t |>.map List.length).sum +
    (OracleBatch.queryTrace P.fromOriginal.controlled.reduction.machine oracle
      (P.fromOriginal.controlled.reduction.machine.init bytes) t |>.map (fun q => (oracle q).length)).sum ≤
        P.fromOriginal.transcriptBitBound.eval bytes.length :=
  ⟨P.fromOriginal.primitives oracle ho x t ht, P.fromOriginal.transcriptBits oracle ho x t ht⟩

theorem toOriginal_prefix_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) oracle)
    (x : ExactSignatureTables.Input P.count 1 P.arity) (t : ℕ)
    (c : P.toOriginal.controlled.reduction.machine.Cfg)
    (ht : t ≤ P.toOriginal.controlled.reduction.time.eval
      ((RawClosedNetwork.validatedEncoding P.count 1 P.arity).encode x).length)
    (hr : P.toOriginal.controlled.reduction.machine.run oracle
      ((RawClosedNetwork.validatedEncoding P.count 1 P.arity).encode x) t = some c) :
    stackSize c.stk ≤ P.toOriginal.storageBound.eval
      ((RawClosedNetwork.validatedEncoding P.count 1 P.arity).encode x).length :=
  P.toOriginal.storage oracle ho x t c ht hr

theorem fromOriginal_prefix_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding P.count 1 P.arity)
      (OI.presentation G).encoding (OriginalLCodec.value P.table) oracle)
    (x : EdgeSubdivision.WireEquivalence.Input s a) (t : ℕ)
    (c : P.fromOriginal.controlled.reduction.machine.Cfg)
    (ht : t ≤ P.fromOriginal.controlled.reduction.time.eval
      ((OriginalForestSource.inputEncoding (s:=s) (arity:=a)).encode x).length)
    (hr : P.fromOriginal.controlled.reduction.machine.run oracle
      ((OriginalForestSource.inputEncoding (s:=s) (arity:=a)).encode x) t = some c) :
    stackSize c.stk ≤ P.fromOriginal.storageBound.eval
      ((OriginalForestSource.inputEncoding (s:=s) (arity:=a)).encode x).length :=
  P.fromOriginal.storage oracle ho x t c ht hr

end Holant.LocalDrafts.RemoteWork.StableClosureV2.Palette
