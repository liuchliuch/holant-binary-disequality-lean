import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6Acquire
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineRealDescent
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineParitySource

/-! Actual whole-current real nonaffine continuation. Full factor restarts
strictly decrease the saved nonaffine-prime minimum at an unchanged group;
all changed groups return the engine's genuine strict defect step. The
universal norm/support/phase producer is invoked with derived family guards. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRealLoop
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
namespace L
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end L
namespace B
export GlobalCloseCompletionKleinAffineLeaf (IsAffine)
end B
namespace R
export GlobalCloseCompletionRetainedPredicateRestart (installed finalPalette)
end R
namespace E
export GlobalCloseCompletionEngineKleinProgramme (restart restrict_same)
end E
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

theorem terminates : ∀k : ℕ,∀base : Palette G,∀A : GeneratedGroupWorklist.Active G base,
    ∀run : GeneratedGroupWorklist.Exhausted G base A,∀noPrior : A.source.done=∅,
    ∀higher : H.Higher G base run,∀cH : OI.K G,∀hcH : cH≠0,
    ∀actualH : Gadget.Realizes run.final.source.palette.family .disequality
      (cH • GlobalCloseCompletionKleinH6RMBell.core),
    ∀old : L.Minimum G run.final.source.palette (B.IsAffine G),old.signature.1=k→
      Nonempty (T.Step G run.final.source.palette run.final.ready.torsion) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro base active run noPrior higher cH hcH actualH old rank
    let P := run.final.source.palette
    have exit4 (output : GlobalCloseCompletionKleinQuaternaryRestart.D.Output G P) :
        Nonempty (T.Step G P run.final.ready.torsion) :=
      GlobalCloseCompletionEngineKleinTransitions.restart_step G P run.final.ready.torsion
        higher.cardinal higher.noncyclic output
    rcases GlobalCloseCompletionKleinStandardNonrealSource.all_real_or_quaternary G P run.final.ready.torsion
      higher.cardinal higher.noncyclic higher.standard run.final.ready.noUnary run.final.ready.noOdd with real|nonreal
    · rcases GlobalCloseCompletionKleinHigherNonaffineParitySource.all_parity_or_quaternary G P run.final.ready.torsion
        higher.cardinal higher.noncyclic higher.standard run.final.ready.noUnary run.final.ready.noOdd with parity|quaternary
      · have domain := GlobalCloseCompletionKleinHigherNonaffinePredicateBounds.nonaffine_prime_domain
          G P run.final.ready.noUnary run.final.ready.noOdd run.final.ready.torsion
          higher.cardinal higher.noncyclic higher.standard old.signature old.retained old.prime old.bad
        let n := old.signature.1-3
        have length : old.signature.1=n+3 := by dsimp [n];omega
        let f : Signature (OI.K G) (n+3) := length ▸ old.signature.2
        have literal : old.signature=(⟨n+3,f⟩ : AnySignature (OI.K G)) :=
          StabilizationMathematical.signature_cast_eq old.signature length
        have retained : (⟨n+3,f⟩ : AnySignature (OI.K G))∈P.family := by simpa only [literal] using old.retained
        have badSig : ¬B.IsAffine G (⟨n+3,f⟩ : AnySignature (OI.K G)) := literal ▸ old.bad
        have bad : ¬Affine (RH.mapSignature (ClosureSourceRows.embedding G) f) := badSig
        have realRetained (g : AnySignature (OI.K G)) (member : g∈P.family) :
            Holant.Pauli.ProjectiveDetermination.IsRealLine
              (RH.mapSignature (ClosurePhysicalBridge.complexEmbedding G) g.2) := by
          obtain ⟨i,rfl⟩ := member
          exact real i
        have parityRetained (g : AnySignature (OI.K G)) (member : g∈P.family) :
            GlobalCloseCompletionProductAncestorParity.PureParity g.2 := by
          obtain ⟨i,rfl⟩ := member
          exact parity i
        have line := realRetained ⟨n+3,f⟩ retained
        have pure := parityRetained ⟨n+3,f⟩ retained
        obtain ⟨c,hc,r,normal⟩ := line
        obtain ⟨cRM,hcRM,actualRM⟩ := GlobalCloseCompletionKleinH6RMActual.rm_actual P.family P.equality cH hcH actualH
        rcases GlobalCloseCompletionKleinHigherNonaffineRealDescent.source G P run.final.ready.torsion
          higher.cardinal higher.noncyclic higher.standard cH hcH actualH cRM hcRM actualRM old f
          (Gadget.realizes_of_mem P.family .disequality f retained) bad (by omega) pure r c hc normal with quaternary|restart
        · obtain ⟨output⟩ := quaternary
          exact exit4 output
        · obtain ⟨q,nonzero,actualQ,new,smaller⟩ := restart
          have positive : 0<(⟨n+3,q⟩ : AnySignature (OI.K G)).1 := by change 0<n+3;omega
          rcases E.restart G P run.final.ready.torsion ⟨n+3,q⟩ nonzero positive actualQ with step|same
          · exact step
          · obtain ⟨S⟩ := same
            rcases _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEngineKleinProgramme.Same.frontier
              G P run.final.ready.torsion ⟨n+3,q⟩ nonzero positive actualQ S higher.cardinal higher.noncyclic with step|newHigher
            · exact step
            · obtain ⟨newHigher⟩ := newHigher
              obtain ⟨new,smaller⟩ : ∃new : L.Minimum G S.run.final.source.palette (B.IsAffine G),
                  new.signature.1<old.signature.1 := by
                rw [←S.palette_eq]
                exact ⟨new,smaller⟩
              obtain ⟨step⟩ := ih new.signature.1 (smaller.trans_eq rank)
                (R.installed G P ⟨n+3,q⟩ nonzero positive actualQ) S.active S.run S.noPrior newHigher
                cH hcH (actualH.mono S.old) new rfl
              exact ⟨E.restrict_same G P run.final.ready.torsion S.run.final.source.palette
                S.run.final.ready.torsion S.old S.group_eq step⟩
      · obtain ⟨output⟩ := quaternary
        exact exit4 output
    · obtain ⟨output⟩ := nonreal
      exact exit4 ⟨output.q,output.actual,output.nonmatching⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRealLoop
end
