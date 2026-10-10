import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.CyclicQ4Resolution
import Holant.Proofs.Dichotomy.Main.PaperControlled.CyclicParityCurrent
import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicHigherExcluded
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopArityTwo
import Holant.Proofs.Closure.GeneratedGroupQ4Consumers

/-! The actual exhausted cyclic marking chooses and consumes its own minimum
and current deck. Higher arities are excluded, six ports install a real
ordinary Eq4 source, and four ports consume the entire finite cyclic restart.
The remaining Eq4, unary, and other-marking interfaces stay explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.CyclicPreparedResolution
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace O
export GlobalCloseCompletionStopOrdinarySource (family tract_iff_current)
end O
namespace R
export PaperControlled.CyclicQ4Resolution (Endpoint resolved)
end R
namespace C
export ClosureMarkedCyclic (NativeCyclic normalized normalize)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

theorem native_cyclic (H : Subgroup (PGL2 ℂ)) (N : C.NativeCyclic H) : IsCyclic H := by
  let e := H.equivMapOfInjective C.normalize.toMonoidHom C.normalize.injective
  apply e.isCyclic.mpr
  change IsCyclic (C.normalized H)
  rw [N.model]
  exact Holant.LocalDrafts.FinitePGL2.cyclicModel_isCyclic N.omega

variable (base : Palette G) {A : GeneratedGroupWorklist.Active G base}
variable (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
variable (N : C.NativeCyclic (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
  ((run.final.source.palette)).family run.final.ready.torsion))

include noPrior N in
theorem exhausted : Nonempty (R.Endpoint G (run.final.source.palette)) := by
  classical
  have cyclic := native_cyclic _ N
  have range : 3≤Nat.card (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
      ((run.final.source.palette)).family run.final.ready.torsion) := by
    rw [N.cardinal]
    exact N.range
  cases GlobalCloseCompletionStopArityTwo.complete G (run.final.source.palette) with
  | small empty _ =>
    exact ⟨.tract (run.final.source.palette) (Set.Subset.refl _) ((O.tract_iff_current G (run.final.source.palette)).mpr
      (FrontierSmallArity.small_native_tractX G (run.final.source.palette) empty))⟩
  | higher data =>
    have high := GlobalCloseCompletionStopArityTwo.large_retained G (run.final.source.palette) data
    obtain ⟨core⟩ := exists_minimumCore ((run.final.source.palette)).family ⟨_,high⟩
    obtain ⟨m,f,proper,even,literal,stable⟩ := GroupPreparedStability.forExhausted G base run noPrior core
    have retained : (⟨m+2,f⟩ : AnySignature (OI.K G))∈((run.final.source.palette)).family := literal ▸ core.retained
    have prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)) := literal ▸ core.prime
    by_cases four : m=2
    · subst m
      exact R.resolved G ⟨(run.final.source.palette),run.final.ready.torsion,f,core,literal,
        run.final.ready.noUnary,run.final.ready.noOdd,stable⟩ range
    by_cases six : m=4
    · subst m
      obtain ⟨P,old,anchor⟩ := PaperControlled.CyclicParityCurrent.six_anchor G (run.final.source.palette)
        run.final.ready.torsion cyclic f retained prime stable
      exact ⟨.anchor P old anchor⟩
    have higher : 8≤m+2 := by obtain ⟨k,hk⟩ := even;omega
    have notTwo : Nat.card (completeGroup ((run.final.source.palette)).family run.final.ready.torsion)≠2 := by
      rw [←ClosureMarkedDihedral.Source.source_cardinal (ClosureSourceRows.embedding G) ((run.final.source.palette)).family run.final.ready.torsion]
      omega
    exact False.elim (GlobalCloseCompletionCyclicHigherExcluded.no_higher ((run.final.source.palette)).family run.final.ready.torsion
      ((run.final.source.palette)).equality (ClosurePhysicalBridge.complexEmbedding G) cyclic f prime higher stable notTwo)

def ForMarking (marking : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    ((run.final.source.palette)).family run.final.ready.torsion) : Prop := match marking with
  | .cyclic _=>Nonempty (R.Endpoint G (run.final.source.palette))
  | _=>True

include noPrior in
theorem forMarking (marking : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    ((run.final.source.palette)).family run.final.ready.torsion) : ForMarking G base run marking := by
  cases marking with
  | cyclic native => exact exhausted G base run noPrior native
  | smallTwo => trivial
  | smallFour => trivial
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

theorem original_current_cyclic_resolution : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.CyclicPreparedResolution
end
