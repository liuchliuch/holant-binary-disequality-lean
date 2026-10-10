import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OddUnary
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopInfiniteOrdinary

/-! Every actual retained odd structural stop enters an existing sourced
unary pipeline. Residual torsion is tested internally: finite-order sources
use the proved odd-to-unary raw-card descent and retained I; otherwise an
actual infinite-order binary supplies its already implemented unary source.
No odd-arity dichotomy or unary terminal classification is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopOddSource
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
namespace O
export GlobalCloseCompletionC2OddUnary
  (palette unary retained unary_nonzero retains_old source)
end O
namespace U
export GlobalCloseCompletionStopUnaryCurrent (Completion)
end U
namespace I
export GlobalCloseCompletionStopInfiniteOrdinary (Completion complete)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

inductive Completion : Type 1 where
  | unary (target : Palette G) (old_retained : P.family⊆target.family)
      (u : Signature (OI.K G) 1) (retained : (⟨1,u⟩ : AnySignature (OI.K G))∈target.family)
      (nonzero : u≠0) (source : U.Completion G target u retained)
  | infinite (B : Binary (K:=OI.K G)) (actual : ActualNonsingular P.family B)
      (infinite : ¬ProjectivelyFinite (transfer B)) (source : I.Completion G P B actual infinite)

variable (f : AnySignature (OI.K G)) (retained : f∈P.family) (nonzero : f.2≠0) (odd : Odd f.1)

def complete : Completion G P := by
  classical
  by_cases tau : ResidualTorsion P.family
  · let actual:=Gadget.realizes_of_mem P.family .disequality f.2 retained
    let identity:=P.retainsIdentity G
    exact .unary (O.palette G P tau identity f.2 actual nonzero odd)
      (O.retains_old G P tau identity f.2 actual nonzero odd)
      (O.unary G P tau identity f.2 actual nonzero odd)
      (O.retained G P tau identity f.2 actual nonzero odd)
      (O.unary_nonzero G P tau identity f.2 actual nonzero odd)
      (O.source G P tau identity f.2 actual nonzero odd)
  · let witness:=(residual_or_actual_infinite P.family).resolve_left tau
    let B:=Classical.choose witness
    have actual:= (Classical.choose_spec witness).1
    have infinite:= (Classical.choose_spec witness).2
    exact .infinite B actual infinite (I.complete G P B actual infinite)

def ForStop (stop : OccurrenceWorklist.Stop G P) : Type 1 :=
  match stop with
  | .odd ..=>Completion G P
  | .unary ..=>PUnit.{2}
  | .infinite ..=>PUnit.{2}
def forStop (stop : OccurrenceWorklist.Stop G P) : ForStop G P stop :=
  match stop with
  | .odd f retained prime _ odd=>complete G P f retained prime.1 odd
  | .unary ..=>PUnit.unit
  | .infinite ..=>PUnit.unit

variable (base : Palette G)
def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 :=
  match result with
  | .initialStop stop _=>ForStop G base stop
  | .prepared _ _ (.inl stopped)=>ForStop G stopped.finalSource.palette stopped.stop
  | .prepared _ _ (.inr _)=>PUnit.{2}
def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop stop _=>forStop G base stop
  | .prepared _ _ (.inl stopped)=>forStop G stopped.finalSource.palette stopped.stop
  | .prepared _ _ (.inr _)=>PUnit.unit
def original_odd_sources : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopOddSource
end
