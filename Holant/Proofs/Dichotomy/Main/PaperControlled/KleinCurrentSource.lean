import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineKleinFrontier
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineKleinProgramme
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineTransitions
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinH6Acquire
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinRealLoop
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineCurrentTract

/-! Universal standard-Pauli whole-current source. All saved rows are consumed:
whole-family affinity gives the actual common-basis tractability criterion;
otherwise a saved nonaffine row acquires actual H6, and full-factor descent
terminates on its retained prime minimum. No manuscript source prerequisite,
universal lower-output closure, or future classifier is an input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinCurrentSource
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace T
export PaperControlled.EngineTransitions (Step)
end T
namespace H
export PaperControlled.EngineKleinFrontier (Higher)
end H
namespace B
export GlobalCloseCompletionKleinAffineLeaf (IsAffine)
end B
namespace L
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum exists_minimum)
end L
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G) {A : GeneratedGroupWorklist.Active G base}
variable (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)

include noPrior in
theorem source (higher : H.Higher G base run) :
    Nonempty (T.Step G run.final.source.palette run.final.ready.torsion) := by
  classical
  let P := run.final.source.palette
  by_cases all : ∀i : Fin P.count,Affine (RH.mapSignature (ClosureSourceRows.embedding G) (P.table i))
  · exact ⟨.tract (GlobalCloseCompletionKleinHigherNonaffineCurrentTract.current_tract G P all)⟩
  · have bad : ∃i : Fin P.count,¬B.IsAffine G ⟨P.arity i.val,P.table i⟩ := by
      simpa only [B.IsAffine,not_forall] using all
    rcases PaperControlled.KleinH6Acquire.source G base run noPrior higher bad with step|resource
    · exact step
    · obtain ⟨S⟩ := resource
      have badNew : ∃j : Fin S.run.final.source.palette.count,
          ¬B.IsAffine G ⟨S.run.final.source.palette.arity j.val,S.run.final.source.palette.table j⟩ := by
        obtain ⟨i,badI⟩ := bad
        obtain ⟨j,hj⟩ := S.old (show (⟨P.arity i.val,P.table i⟩ : AnySignature (OI.K G))∈P.family from ⟨i,rfl⟩)
        exact ⟨j,fun h=>badI (hj ▸ h)⟩
      obtain ⟨old⟩ := L.exists_minimum G S.run.final.source.palette (B.IsAffine G)
        (GlobalCloseCompletionKleinHigherNonaffineFactorRestart.affine_split_closed G) badNew
      obtain ⟨step⟩ := PaperControlled.KleinRealLoop.terminates G old.signature.1
        S.base S.active S.run S.noPrior S.higher S.scale S.nonzero S.actual old rfl
      exact ⟨PaperControlled.EngineKleinProgramme.restrict_same G P run.final.ready.torsion
        S.run.final.source.palette S.run.final.ready.torsion S.old S.group_eq step⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinCurrentSource
end
