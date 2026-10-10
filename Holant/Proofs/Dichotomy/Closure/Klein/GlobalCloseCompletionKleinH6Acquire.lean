import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6Prepared
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterCurrentDescent

/-! A retained nonaffine row and the proved stable RM source supply actual
H6 after one genuine full-factor restart. The original nonaffine row is saved;
non-character descent is used solely to obtain this additional resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6Acquire
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
namespace T
export GlobalCloseCompletionEngineTransitions (Step)
end T
namespace H
export GlobalCloseCompletionEngineKleinFrontier (Higher)
end H
namespace C
export GlobalCloseCompletionRetainedCharacterLeaf (Predicate)
end C
namespace R
export GlobalCloseCompletionRetainedPredicateRestart (installed finalPalette output_retained)
end R
namespace E
export GlobalCloseCompletionEngineKleinProgramme (Same restart restrict_same)
end E
namespace L
export GlobalCloseCompletionKleinAffineLeaf (IsAffine)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

structure State (P : Palette G) (torsion : ResidualTorsion P.family) where
  base : Palette G
  active : GeneratedGroupWorklist.Active G base
  run : GeneratedGroupWorklist.Exhausted G base active
  noPrior : active.source.done=∅
  old : P.family⊆run.final.source.palette.family
  group_eq : completeGroup run.final.source.palette.family run.final.ready.torsion=completeGroup P.family torsion
  higher : H.Higher G base run
  scale : OI.K G
  nonzero : scale≠0
  actual : Gadget.Realizes run.final.source.palette.family .disequality
    (scale • GlobalCloseCompletionKleinH6RMBell.core)

variable (base : Palette G) {A : GeneratedGroupWorklist.Active G base}
variable (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)

include noPrior in
theorem source (higher : H.Higher G base run)
    (bad : ∃i : Fin run.final.source.palette.count,
      ¬L.IsAffine G ⟨run.final.source.palette.arity i.val,run.final.source.palette.table i⟩) :
    Nonempty (T.Step G run.final.source.palette run.final.ready.torsion) ∨
      Nonempty (State G run.final.source.palette run.final.ready.torsion) := by
  let P := run.final.source.palette
  have prime : Prime (⟨higher.m+2,higher.f⟩ : AnySignature (OI.K G)) := by
    simpa only [higher.literal] using higher.core.prime
  have retained : (⟨higher.m+2,higher.f⟩ : AnySignature (OI.K G))∈P.family := by
    simpa only [higher.literal] using higher.core.retained
  have actualF := Gadget.realizes_of_mem P.family .disequality higher.f retained
  rcases GlobalCloseCompletionKleinStandardCoreResource.source G P run.final.ready.torsion
    higher.cardinal higher.noncyclic higher.standard higher.f higher.higher higher.even prime actualF higher.stable with rm|q4
  · obtain ⟨c,hc,actualRM⟩ := rm
    obtain ⟨i,badI⟩ := bad
    have noncharacter : ¬C.Predicate G ⟨P.arity i.val,P.table i⟩ := by
      intro flat
      apply badI
      exact Holant.ReedMuller.TwoChart.affine_of_CFlat _ flat
    obtain ⟨q,small,nonzero,positive,actualQ,badQ⟩ :=
      GlobalCloseCompletionKleinCharacterCurrentDescent.small_or_odd G P run.final.ready.torsion
        higher.cardinal higher.noncyclic higher.standard c hc actualRM (P.table i)
        (Gadget.realizes_of_mem P.family .disequality (P.table i) ⟨i,rfl⟩) noncharacter
    rcases E.restart G P run.final.ready.torsion q nonzero positive actualQ with step|same
    · exact Or.inl step
    · obtain ⟨S⟩ := same
      rcases _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEngineKleinProgramme.Same.frontier G P run.final.ready.torsion q nonzero positive actualQ S
        higher.cardinal higher.noncyclic with step|newHigher
      · exact Or.inl step
      · obtain ⟨newHigher⟩ := newHigher
        have retainedQ : q∈S.run.final.source.palette.family := by
          rw [←S.palette_eq]
          exact R.output_retained G P q nonzero positive actualQ
        have evenQ := GlobalCloseCompletionKleinHigherNonaffinePredicateBounds.retained_even G S.run.final.source.palette
          S.run.final.ready.noUnary S.run.final.ready.noOdd q retainedQ
        have bound : q.1≤8 := by
          rcases small with small|odd
          · exact small
          · obtain ⟨j,hj⟩ := evenQ
            obtain ⟨k,hk⟩ := odd
            omega
        rcases GlobalCloseCompletionKleinH6Prepared.source G (R.installed G P q nonzero positive actualQ)
          S.run S.noPrior newHigher q retainedQ bound badQ with h6|step
        · obtain ⟨d,hd,actualH⟩ := h6
          exact Or.inr ⟨⟨_,_,S.run,S.noPrior,S.old,S.group_eq,newHigher,d,hd,actualH⟩⟩
        · obtain ⟨step⟩ := step
          exact Or.inl ⟨E.restrict_same G P run.final.ready.torsion S.run.final.source.palette
            S.run.final.ready.torsion S.old S.group_eq step⟩
  · obtain ⟨q,_live,actualQ,nonmatching⟩ := q4
    exact Or.inl (GlobalCloseCompletionEngineKleinTransitions.restart_step G P run.final.ready.torsion
      higher.cardinal higher.noncyclic ⟨q,actualQ,nonmatching⟩)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6Acquire
end
