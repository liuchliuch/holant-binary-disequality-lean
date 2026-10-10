import Holant.Proofs.FiniteGroups.Stabilization.ResolvingExecution.RetainedBranches
import Holant.Proofs.Reductions.OriginalFrozenForest.OriginalInput
import Holant.Complexity.OracleBatch.PrimitiveCost
import Holant.Complexity.OracleBatch.QueryTrace
import Holant.Complexity.OracleSpace

/-! Version 2 SPECIFICATION ONLY, in the original Holant project vocabulary.
No stabilization, batch compiler or global closure proof is supplied here.
The returned palette has real two-way controlled programmes to ORIGINAL G.
All scalars and tables live in the coefficient field fixed from that G.
Structural obstruction witnesses are not complexity or rigidity theorems. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant Holant.Algebraic Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.Certificates.MatchingContractionClosure
open Computability

/-- OUTPUT cost certificate for the SAME real programme and original input
bytes. Every oracle extension and every certified execution prefix is covered.
It charges ordinary primitives, outgoing/incoming oracle bits and live stacks. -/
structure PhysicalProgramme {α β γ δ : Type}
    (ea : Encoding α Bool) (eb : Encoding β Bool)
    (ec : Encoding γ Bool) (ed : Encoding δ Bool)
    (f : α → β) (g : γ → δ) where
  controlled : LengthControlledOracleReduction ea eb ec ed f g
  primitiveBound : Polynomial ℕ
  transcriptBitBound : Polynomial ℕ
  storageBound : Polynomial ℕ
  primitives : ∀ oracle, RepresentsOracle ec ed g oracle → ∀ x t,
    t ≤ controlled.reduction.time.eval (ea.encode x).length →
      OracleBatch.primitiveCount controlled.reduction.machine oracle
        (controlled.reduction.machine.init (ea.encode x)) t ≤
          primitiveBound.eval (ea.encode x).length
  transcriptBits : ∀ oracle, RepresentsOracle ec ed g oracle → ∀ x t,
    t ≤ controlled.reduction.time.eval (ea.encode x).length →
      ((OracleBatch.queryTrace controlled.reduction.machine oracle
        (controlled.reduction.machine.init (ea.encode x)) t).map List.length).sum +
      ((OracleBatch.queryTrace controlled.reduction.machine oracle
        (controlled.reduction.machine.init (ea.encode x)) t).map
          (fun q => (oracle q).length)).sum ≤ transcriptBitBound.eval (ea.encode x).length
  storage : ∀ oracle, RepresentsOracle ec ed g oracle → ∀ x t
    (c : controlled.reduction.machine.Cfg),
    t ≤ controlled.reduction.time.eval (ea.encode x).length →
    controlled.reduction.machine.run oracle (ea.encode x) t = some c →
      stackSize c.stk ≤ storageBound.eval (ea.encode x).length
namespace OI
export Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput
  (K numberField publicTable count arity family storedTrees presentation)
end OI
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- OUTPUT type. The receiving worker must construct both programmes;
neither programme, a complete deck, nor a successful branch is caller input. -/
structure Palette where
  count : ℕ
  arity : ℕ → ℕ
  table : (i : Fin count) → Signature (OI.K G) (arity i.val)
  positive : ∀ i : Fin count, 0 < arity i.val
  nonzero : ∀ i : Fin count, table i ≠ 0
  trees : ∀ i : Fin count, FactorTree (⟨arity i.val, table i⟩ : AnySignature (OI.K G))
  leavesRetained : ∀ i : Fin count, ∀ f ∈ (trees i).leaves,
    f ∈ Set.range (fun j : Fin count => (⟨arity j.val, table j⟩ : AnySignature (OI.K G)))
  originalSaved : ∀ i : Fin (OI.count G), ∃ j : Fin count,
    (⟨⟨arity j.val, table j⟩, trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨OI.arity G i.val, OI.publicTable G i⟩, OI.storedTrees G i⟩
  equality : (⟨2, binarySignature Signature.equality⟩ : AnySignature (OI.K G)) ∈
    Set.range (fun i : Fin count => (⟨arity i.val, table i⟩ : AnySignature (OI.K G)))
  toOriginal : PhysicalProgramme
    (RawClosedNetwork.validatedEncoding count 1 arity) (OI.presentation G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding
    (OriginalLCodec.value table) (OriginalForestSource.value G)
  fromOriginal : PhysicalProgramme
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding
    (RawClosedNetwork.validatedEncoding count 1 arity) (OI.presentation G).encoding
    (OriginalForestSource.value G) (OriginalLCodec.value table)

def Palette.family (P : Palette G) : SignatureFamily (OI.K G) :=
  Set.range (fun i : Fin P.count => (⟨P.arity i.val, P.table i⟩ : AnySignature (OI.K G)))

/-- Source-grounded structural leaves. An odd/unary/infinite leaf is genuine
data over the returned CURRENT family, not an assumed hardness theorem. -/
inductive StructuralExit (P : Palette G) : Type
  | unary (u : Signature (OI.K G) 1)
      (retained : (⟨1,u⟩ : AnySignature (OI.K G)) ∈ P.family) (nonzero : u ≠ 0)
  | infinite (B : Holant.Certificates.MatchingContractionClosure.Binary (K:=OI.K G))
      (actual : Holant.Projective.BoundedTorsion.ActualNonsingular P.family B)
      (infiniteOrder : ¬ Holant.Projective.BoundedTorsion.ProjectivelyFinite
        (Holant.Certificates.MatchingContractionClosure.transfer B))
  | odd (f : AnySignature (OI.K G)) (retained : f ∈ P.family)
      (prime : Prime f) (nonbinary : 3 ≤ f.1) (oddArity : Odd f.1)
  | stable (m : ℕ) (f : Signature (OI.K G) (m+2)) (proper : 2 ≤ m)
      (evenArity : Even (m+2)) (torsion : ResidualTorsion P.family)
      (minimum : MinimumCore P.family) (core : minimum.signature = ⟨m+2,f⟩)
      (noUnary : ¬ RetainedUnary P.family)
      (noOdd : ∀ g ∈ P.family, Prime g → 3 ≤ g.1 → Even g.1)
      (regeneratedDeck : ∀ g ∈ rawDeck P.family torsion f,
        MatchingOrZero (Holant.Projective.BoundedTorsion.actualTransfers P.family) g)

structure StabilizationResult where
  palette : Palette G
  exit : StructuralExit G palette

/-- OPEN all-arity source-facing stabilization. Smaller arity/group growth
are continuing transitions, never final constructors of StructuralExit. -/
def OriginalStabilizationGoal : Prop :=
  ∀ (s : ℕ) (a : ℕ → ℕ)
    (G : (i : Fin s) → Signature AlgebraicComplex (a i.val)),
    ∀ (_torsion : ResidualTorsion (OI.family G)) (core : MinimumCore (OI.family G)),
      4 ≤ core.signature.1 → Even core.signature.1 → Nonempty (StabilizationResult G)

attribute [local instance] Classical.propDecidable

/-- OPEN batch OUTPUT. Its queue is the FULL literal raw-card catalogue,
with the SAME once-saved trees. Original scalars, ports and old trees persist. -/
structure DeckBatchResult (P : Palette G) (torsion : ResidualTorsion P.family)
    {m : ℕ} (f : Signature (OI.K G) (m+2)) where
  palette : Palette G
  oldSaved : ∀ i : Fin P.count, ∃ j : Fin palette.count,
    (⟨⟨palette.arity j.val,palette.table j⟩,palette.trees j⟩ : TreeOccurrence (OI.K G)) =
      ⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩
  deckSaved : ∀ k : FullDeckIndex P.family torsion f, ∃ j : Fin palette.count,
    (⟨⟨palette.arity j.val,palette.table j⟩,palette.trees j⟩ : TreeOccurrence (OI.K G)) =
      fullDeckRoot P.family torsion f k
  finalQueue : FrozenQueue (OI.K G) (fullDeckUniverse P.family torsion f)
  queueRun : FrozenQueue.Runs
    (FrozenQueue.initial (fullDeckUniverse P.family torsion f)
      (fullDeckRoot P.family torsion f)) finalQueue
  exhausted : finalQueue.todo = ∅
  allDone : finalQueue.done = fullDeckUniverse P.family torsion f

/-- OPEN producer, not a backend parameter for OriginalStabilizationGoal.
P carries only already established SOURCE programmes. The worker constructs
new full-deck programmes, exact saved-tree bindings and actual queue runs. -/
def CompleteDeckBatchGoal : Prop :=
  ∀ (s : ℕ) (a : ℕ → ℕ)
    (G : (i : Fin s) → Signature AlgebraicComplex (a i.val)) (P : Palette G),
    ∀ (torsion : ResidualTorsion P.family) (m : ℕ)
      (f : Signature (OI.K G) (m+2)) (core : MinimumCore P.family),
      2 ≤ m → Even (m+2) → core.signature = ⟨m+2,f⟩ →
        Nonempty (DeckBatchResult G P torsion f)

end Holant.LocalDrafts.RemoteWork.StableClosureV2
end
