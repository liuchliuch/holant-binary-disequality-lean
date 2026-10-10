import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2UnaryFrontier
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2PrimeClassification
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopArityTwo
import Holant.Proofs.Closure.GeneratedGroupQ4Consumers

/-! The actual exhausted smallTwo marking supplies its own saved minimum,
regenerated matching deck and, in the higher branch, actual scalar RM graph.
The complete family then reaches a real Eq4 source, a genuine tractable/hard
answer, or a strictly decreasing retained-counterexample restart. No RM graph,
chosen q4, minimum, deck, or unary-handler hypothesis is supplied by callers.
The source/restart alternatives are deliberately not called final terminals. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PreparedFrontier
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace O
export GlobalCloseCompletionStopOrdinarySource (family table tract_iff_current)
end O
namespace F
export GlobalCloseCompletionRetainedFlatLeaf (Predicate)
end F
namespace B
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end B
namespace R
export GlobalCloseCompletionC2FlatRestart (Output)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

def Frontier : Prop := Tract (O.family G P) ∨ NoXWeightedAntiSquares.Hard G ∨
  GlobalCloseCompletionC2OrdinaryPairOutcome.HasEq4 (O.table G P) ∨
  ∃M : B.Minimum G P (F.Predicate G),Nonempty (R.Output G P M)

theorem unary_minimum (M : B.Minimum G P (F.Predicate G)) (one : M.signature.1=1) : RetainedUnary P.family := by
  generalize literal : M.signature=q at one
  obtain ⟨n,u⟩ := q
  dsimp at one
  subst n
  refine ⟨u,literal ▸ M.retained,?_⟩
  have prime : Prime (⟨1,u⟩ : AnySignature (OI.K G)) := literal ▸ M.prime
  exact prime.1

variable (base : Palette G) {A : GeneratedGroupWorklist.Active G base}
variable (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
local notation "Q" => run.final.source.palette

include noPrior in
theorem exhausted (cardTwo : Nat.card (completeGroup (Q).family run.final.ready.torsion)=2) : Frontier G Q := by
  classical
  cases GlobalCloseCompletionStopArityTwo.complete G Q with
  | small empty _ =>
    exact Or.inl ((O.tract_iff_current G Q).mpr (FrontierSmallArity.small_native_tractX G Q empty))
  | higher data =>
    have high := GlobalCloseCompletionStopArityTwo.large_retained G Q data
    obtain ⟨core⟩ := exists_minimumCore (Q).family ⟨_,high⟩
    obtain ⟨m,f,proper,even,literal,stable⟩ := GroupPreparedStability.forExhausted G base run noPrior core
    have retained : (⟨m+2,f⟩ : AnySignature (OI.K G))∈(Q).family := literal ▸ core.retained
    have prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)) := literal ▸ core.prime
    rcases GlobalCloseCompletionC2PrimeClassification.current_prime_classification (Q).family run.final.ready.torsion
      (Q).equality cardTwo (ClosureSourceRows.embedding G) f proper even prime stable with four|⟨eight,_⟩
    · subst m
      rcases GlobalCloseCompletionC2PrimeCurrent.classified G Q run.final.ready.torsion (Q).equality cardTwo
        f retained prime stable with anchor|tract|hard
      · exact Or.inr (Or.inr (Or.inl anchor))
      · exact Or.inl tract
      · exact Or.inr (Or.inl hard)
    · subst m
      obtain ⟨c,hc,actualRM⟩ := GlobalCloseCompletionC2RMActual.current_actual (Q).family run.final.ready.torsion
        (Q).equality cardTwo (ClosurePhysicalBridge.complexEmbedding G) f retained prime stable
      rcases GlobalCloseCompletionC2UnaryFrontier.frontier G Q run.final.ready.torsion (Q).equality cardTwo c hc actualRM with
        tract|hard|anchor|⟨M,one|restart⟩
      · exact Or.inl tract
      · exact Or.inr (Or.inl hard)
      · exact Or.inr (Or.inr (Or.inl anchor))
      · exact False.elim (run.final.ready.noUnary (unary_minimum G Q M one))
      · exact Or.inr (Or.inr (Or.inr ⟨M,restart⟩))

def ForMarking (marking : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (Q).family run.final.ready.torsion) : Prop := match marking with
  | .smallTwo _=>Frontier G Q
  | _=>True

include noPrior in
theorem forMarking (marking : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (Q).family run.final.ready.torsion) : ForMarking G base run marking := by
  cases marking with
  | smallTwo card =>
    apply exhausted G base run noPrior
    rw [←ClosureMarkedDihedral.Source.source_cardinal (ClosureSourceRows.embedding G) (Q).family run.final.ready.torsion]
    exact card
  | smallFour => trivial
  | cyclic => trivial
  | monomial => trivial
  | bilinear => trivial
  | unshifted => trivial
  | shifted => trivial
  | platonic => trivial

def ForResult (result : GeneratedGroupWorklist.Result G base) : Prop := match result with
  | .initialStop ..=>True
  | .prepared _ _ (.inl _)=>True
  | .prepared _ _ (.inr run)=>ForMarking G base run
      (ClosureMarkedActualReceipts.produce G run.final.source.palette run.final.ready.torsion).physical.marking

theorem forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := by
  cases result with
  | initialStop => trivial
  | prepared ready trace result =>
    cases result with
    | inl => trivial
    | inr run => exact forMarking G base run rfl _

theorem original_current_c2_frontier : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PreparedFrontier
end
