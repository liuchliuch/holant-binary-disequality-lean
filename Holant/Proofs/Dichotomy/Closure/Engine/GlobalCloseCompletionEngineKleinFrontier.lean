import Holant.Proofs.Dichotomy.Closure.Engine.GlobalCloseCompletionEngineTransitions
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinExoticFull
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinQuaternaryResolved

/-! Select the actual prepared Klein minimum and consume all small,
quaternary, and exotic cases. The remaining source is explicitly standard,
even and of arity at least six, with the whole exhausted run retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEngineKleinFrontier
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
namespace T
export GlobalCloseCompletionEngineTransitions (CurrentTract Hard)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G) {A : GeneratedGroupWorklist.Active G base}
variable (run : GeneratedGroupWorklist.Exhausted G base A)

structure Higher where
  cardinal : Nat.card (completeGroup run.final.source.palette.family run.final.ready.torsion)=4
  noncyclic : ¬IsCyclic (completeGroup run.final.source.palette.family run.final.ready.torsion)
  standard : ClosureKleinCurrent.kind G run.final.source.palette run.final.ready.torsion cardinal noncyclic=.standard
  m : ℕ
  f : Signature (OI.K G) (m+2)
  proper : 2≤m
  even : Even (m+2)
  higher : 6≤m+2
  core : MinimumCore run.final.source.palette.family
  literal : core.signature=⟨m+2,f⟩
  stable : ∀g∈rawDeck run.final.source.palette.family run.final.ready.torsion f,
    MatchingOrZero (actualTransfers run.final.source.palette.family) g

theorem exhausted (noPrior : A.source.done=∅)
    (four : Nat.card (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
      run.final.source.palette.family run.final.ready.torsion)=4)
    (noncyclic : ¬IsCyclic (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
      run.final.source.palette.family run.final.ready.torsion)) :
    T.CurrentTract G run.final.source.palette ∨ T.Hard G ∨ Nonempty (Higher G base run) := by
  have cardinal : Nat.card (completeGroup run.final.source.palette.family run.final.ready.torsion)=4 := by
    rw [←ClosureMarkedDihedral.Source.source_cardinal (ClosureSourceRows.embedding G)
      run.final.source.palette.family run.final.ready.torsion]
    exact four
  have nativeNoncyclic := ClosureFieldBridgeEquiv.source_not_isCyclic (ClosureSourceRows.embedding G)
    run.final.source.palette.family run.final.ready.torsion noncyclic
  cases GlobalCloseCompletionStopArityTwo.complete G run.final.source.palette with
  | small empty _ =>
    exact Or.inl (FrontierSmallArity.small_native_tractX G run.final.source.palette empty)
  | higher data =>
    have high := GlobalCloseCompletionStopArityTwo.large_retained G run.final.source.palette data
    obtain ⟨core⟩ := exists_minimumCore run.final.source.palette.family ⟨_,high⟩
    obtain ⟨m,f,proper,even,literal,stable⟩ := GroupPreparedStability.forExhausted G base run noPrior core
    by_cases small : m=2
    · subst m
      rcases GlobalCloseCompletionKleinQuaternaryResolved.classified G run.final.source.palette
        run.final.ready.torsion cardinal nativeNoncyclic f core literal stable with tract|hard
      · exact Or.inl tract
      · exact Or.inr (Or.inl hard)
    · cases kind : ClosureKleinCurrent.kind G run.final.source.palette run.final.ready.torsion cardinal nativeNoncyclic with
      | standard =>
        have higher : 6≤m+2 := by obtain ⟨k,hk⟩ := even; omega
        exact Or.inr (Or.inr ⟨⟨cardinal,nativeNoncyclic,kind,m,f,proper,even,higher,core,literal,stable⟩⟩)
      | exotic =>
        rcases GlobalCloseCompletionKleinExoticFull.classified G run.final.source.palette
          run.final.ready.torsion cardinal nativeNoncyclic kind f proper even core literal stable with tract|hard
        · exact Or.inl tract
        · exact Or.inr (Or.inl hard)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEngineKleinFrontier
end
