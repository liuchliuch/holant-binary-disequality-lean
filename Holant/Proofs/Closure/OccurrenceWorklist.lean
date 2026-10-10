import Holant.Proofs.Closure.FrontierCurrent
import Holant.Proofs.Closure.OccurrenceBatchJointLeaves
import Holant.Proofs.Closure.StabilizationMathematical

/-! Cumulative finite preparation of immutable saved prime occurrences.
The outer rank counts unvisited addresses. Every even nonbinary preparation
runs the actual current-source retained batch with its joint physical trace.
Local classification remains pending, including every newly retained prime. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

/-- The root map preserves labels as well as the entire once-saved tree.
Immutable occurrence IDs are never replaced by equal-valued new leaves. -/
structure State where
  palette : Palette G
  rootLabel : Fin base.count → Fin palette.count
  rootInjective : Function.Injective rootLabel
  rootSaved : ∀ i, Frontier.paletteRoot G palette (rootLabel i) = Frontier.paletteRoot G base i
  todo : Finset (CurrentOccurrences.Id G base)

def initial : State G base := ⟨base,id,Function.injective_id,fun _ => rfl,Finset.univ⟩

def State.currentId (S : State G base) (o : CurrentOccurrences.Id G base) :
    CurrentOccurrences.Id G S.palette :=
  ⟨S.rootLabel o.1,Occurrences.transportAddress (S.rootSaved o.1).symm o.2⟩

theorem State.leafExact (S : State G base) (o : CurrentOccurrences.Id G base) :
    CurrentOccurrences.savedLeaf G S.palette (S.currentId G base o) =
      CurrentOccurrences.savedLeaf G base o :=
  Occurrences.transportAddress_leaf (S.rootSaved o.1).symm o.2

theorem State.currentId_injective (S : State G base) :
    Function.Injective (S.currentId G base) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ h
  have hi : S.rootLabel i = S.rootLabel j := congrArg Sigma.fst h
  have hij := S.rootInjective hi
  subst j
  have hp : Occurrences.transportAddress (S.rootSaved i).symm p =
      Occurrences.transportAddress (S.rootSaved i).symm q :=
    @sigma_mk_injective (Fin S.palette.count)
      (fun k => Occurrences.Address (S.palette.trees k)) (S.rootLabel i) _ _ h
  exact Sigma.ext rfl (heq_of_eq (Occurrences.transportAddress_injective (S.rootSaved i).symm hp))

def State.domain (S : State G base) (o : CurrentOccurrences.Id G base) :=
  CurrentOccurrences.domain G S.palette (S.currentId G base o)

@[simp] theorem State.domain_pending (S : State G base) (o : CurrentOccurrences.Id G base) :
    (S.domain G base o).preparation = Frontier.Preparation.pending := rfl

def State.erase (S : State G base) (o : CurrentOccurrences.Id G base) : State G base :=
  { S with todo := S.todo.erase o }

/-- A genuine current-source structural exit; no local hardness theorem is
asserted and stable is not used as a stop for this outer occurrence pass. -/
inductive Stop (P : Palette G) : Type
  | unary (u : Signature (OI.K G) 1) (retained : (⟨1,u⟩ : AnySignature (OI.K G)) ∈ P.family)
      (nonzero : u ≠ 0)
  | infinite (B : Binary (K:=OI.K G)) (actual : ActualNonsingular P.family B)
      (infiniteOrder : ¬ ProjectivelyFinite (transfer B))
  | odd (f : AnySignature (OI.K G)) (retained : f ∈ P.family) (prime : Prime f)
      (nonbinary : 3 ≤ f.1) (oddArity : Odd f.1)

structure Ready (P : Palette G) : Type where
  torsion : ResidualTorsion P.family
  noUnary : ¬ RetainedUnary P.family
  noOdd : StabilizationMathematical.NoOdd P.family

def Ready.group {P : Palette G} (r : Ready G P) := completeGroup P.family r.torsion

def inspect (P : Palette G) : Stop G P ⊕ Ready G P := by
  by_cases hu : RetainedUnary P.family
  · exact .inl (.unary (Classical.choose hu) (Classical.choose_spec hu).1 (Classical.choose_spec hu).2)
  by_cases ht : ResidualTorsion P.family
  · by_cases ho : ∃ f ∈ P.family, Prime f ∧ 3 ≤ f.1 ∧ Odd f.1
    · exact .inl (.odd (Classical.choose ho) (Classical.choose_spec ho).1
        (Classical.choose_spec ho).2.1 (Classical.choose_spec ho).2.2.1
        (Classical.choose_spec ho).2.2.2)
    · exact .inr ⟨ht,hu,StabilizationMathematical.noOdd_of_absent ho⟩
  · let witness := (residual_or_actual_infinite P.family).resolve_left ht
    exact .inl (.infinite (Classical.choose witness) (Classical.choose_spec witness).1
      (Classical.choose_spec witness).2)

def Stop.structural {P : Palette G} : Stop G P → StructuralExit G P
  | .unary u h hn => .unary u h hn
  | .infinite b h hi => .infinite b h hi
  | .odd f h hp hn ho => .odd f h hp hn ho

/-- Exact selected occurrence data, with retained membership at the CURRENT
palette. Its even arity is never promoted to a MinimumCore premise. -/
structure BatchInput (S : State G base) (o : CurrentOccurrences.Id G base) where
  m : ℕ
  signature : Signature (OI.K G) (m+2)
  literal : (⟨m+2,signature⟩ : AnySignature (OI.K G)) = (CurrentOccurrences.savedLeaf G base o).1
  proper : 2 ≤ m
  evenArity : Even (m+2)
  retained : (⟨m+2,signature⟩ : AnySignature (OI.K G)) ∈ S.palette.family

def batchInput (S : State G base) (o : CurrentOccurrences.Id G base)
    (hf : 4 ≤ (CurrentOccurrences.savedLeaf G base o).1.1)
    (he : Even (CurrentOccurrences.savedLeaf G base o).1.1) : BatchInput G base S o := by
  let q := (CurrentOccurrences.savedLeaf G base o).1
  let m := q.1 - 2
  have hn : q.1 = m+2 := by dsimp [m,q]; omega
  let f : Signature (OI.K G) (m+2) := hn ▸ q.2
  have hq : q = (⟨m+2,f⟩ : AnySignature (OI.K G)) :=
    StabilizationMathematical.signature_cast_eq q hn
  refine ⟨m,f,hq.symm,by dsimp [m,q]; omega,?_,?_⟩
  · simpa only [← hn] using he
  · rw [← hq]
    change (CurrentOccurrences.savedLeaf G base o).1 ∈ S.palette.family
    rw [← S.leafExact G base o]
    exact CurrentOccurrences.savedLeaf_retained G S.palette (S.currentId G base o)

def State.batch (S : State G base) (o : CurrentOccurrences.Id G base)
    (b : BatchInput G base S o) (torsion : ResidualTorsion S.palette.family) : State G base where
  palette := OccurrenceBatch.palette G S.palette torsion b.signature b.retained b.proper
  rootLabel i := RetainedCatalogue.oldLabel G S.palette torsion b.signature (S.rootLabel i)
  rootInjective := by
    intro i j h
    apply S.rootInjective
    apply Fin.ext
    exact congrArg (fun x : Fin (RetainedCatalogue.count G S.palette torsion b.signature) => x.val) h
  rootSaved i := (RetainedCatalogue.old_saved G S.palette torsion b.signature (S.rootLabel i)).trans
    (S.rootSaved i)
  todo := S.todo.erase o

/-- The minimum is recomputed on the actual augmented family. This data is
recorded without a sourceOmega descent claim for the selected occurrence. -/
def batchMinimum (S : State G base) (o : CurrentOccurrences.Id G base)
    (b : BatchInput G base S o) (torsion : ResidualTorsion S.palette.family) :
    MinimumCore (S.batch G base o b torsion).palette.family := by
  let q := (CurrentOccurrences.savedLeaf G base o).1
  have retained : q ∈ (S.batch G base o b torsion).palette.family := by
    change q ∈ (OccurrenceBatch.palette G S.palette torsion b.signature b.retained b.proper).family
    rw [OccurrenceBatch.family_exact]
    exact fullRetainedDeck_retains S.palette.family torsion b.signature
      (by change (CurrentOccurrences.savedLeaf G base o).1 ∈ S.palette.family
          rw [← b.literal]; exact b.retained)
  have prime : Prime q := CurrentOccurrences.savedLeaf_prime G base o
  have proper : 3 ≤ q.1 := by
    have h : b.m+2 = q.1 := congrArg Sigma.fst b.literal
    have hm := b.proper
    omega
  exact Classical.choice (exists_minimumCore _ ⟨q,retained,prime,proper⟩)

/-- Concrete complete-batch and SAME tagged physical receipts; no compiler,
future worklist or transition-coverage policy is a caller argument. -/
structure BatchReceipt (S : State G base) (o : CurrentOccurrences.Id G base)
    (b : BatchInput G base S o) (torsion : ResidualTorsion S.palette.family) : Type 1 where
  domain : CurrentOccurrences.Domain G S.palette (S.currentId G base o)
  domainIdentity : domain = S.domain G base o
  batch : DeckBatchResult G S.palette torsion b.signature
  batchIdentity : batch = OccurrenceBatch.result G S.palette torsion b.signature b.retained b.proper
  paletteIdentity : batch.palette = (S.batch G base o b torsion).palette
  joint : OccurrenceBatchJoint.TaggedJointTrace G S.palette torsion b.signature b.retained b.proper true
    (FullQueue.taggedExecution G S.palette torsion b.signature).trace
  jointIdentity : joint = OccurrenceBatchJoint.savedTaggedJoint G S.palette torsion b.signature b.retained b.proper
  jointLeaves : OccurrenceBatchJointLeaves.JointTraceWithLeaves G S.palette torsion b.signature b.retained b.proper true
    (FullQueue.taggedExecution G S.palette torsion b.signature).trace
  jointLeavesIdentity : jointLeaves = OccurrenceBatchJointLeaves.savedJointWithLeaves G S.palette torsion b.signature b.retained b.proper
  minimum : MinimumCore (S.batch G base o b torsion).palette.family
  minimumIdentity : minimum = batchMinimum G base S o b torsion
  post : Stop G (S.batch G base o b torsion).palette ⊕ Ready G (S.batch G base o b torsion).palette
  postIdentity : post = inspect G (S.batch G base o b torsion).palette

def batchReceipt (S : State G base) (o : CurrentOccurrences.Id G base)
    (b : BatchInput G base S o) (torsion : ResidualTorsion S.palette.family) :
    BatchReceipt G base S o b torsion :=
  ⟨S.domain G base o,rfl,OccurrenceBatch.result G S.palette torsion b.signature b.retained b.proper,rfl,rfl,
    OccurrenceBatchJoint.savedTaggedJoint G S.palette torsion b.signature b.retained b.proper,rfl,
    OccurrenceBatchJointLeaves.savedJointWithLeaves G S.palette torsion b.signature b.retained b.proper,rfl,
    batchMinimum G base S o b torsion,rfl,inspect G (S.batch G base o b torsion).palette,rfl⟩

theorem BatchInput.currentLiteral (S : State G base) (o : CurrentOccurrences.Id G base)
    (b : BatchInput G base S o) :
    (⟨b.m+2,b.signature⟩ : AnySignature (OI.K G)) =
      (CurrentOccurrences.savedLeaf G S.palette (S.currentId G base o)).1 :=
  b.literal.trans (congrArg Sigma.fst (S.leafExact G base o)).symm

theorem BatchReceipt.domain_pending (S : State G base) (o : CurrentOccurrences.Id G base)
    (b : BatchInput G base S o) (torsion : ResidualTorsion S.palette.family)
    (r : BatchReceipt G base S o b torsion) : r.domain.preparation = Frontier.Preparation.pending := by
  rw [r.domainIdentity]
  rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceWorklist
