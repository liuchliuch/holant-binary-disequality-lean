import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineKleinFrontier
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineKleinTransitions
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineTransitions
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.EngineKleinProgramme
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardCoreResource
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightCharacter
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffinePredicateBounds

/-! An actual prepared standard source retaining a small non-character-flat
row supplies actual H6, or an already consumable engine step. A bad eight-port
prime is made an actual final minimum before its deck is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinH6Prepared
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
namespace T
export PaperControlled.EngineTransitions (Step)
end T
namespace H
export PaperControlled.EngineKleinFrontier (Higher)
end H
namespace C
export GlobalCloseCompletionRetainedCharacterLeaf (Predicate exists_minimum split_closed)
end C
namespace L
export GlobalCloseCompletionRetainedPredicateLeaf (Minimum)
end L
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
theorem source (higher : H.Higher G base run) (q : AnySignature (OI.K G))
    (retained : q∈run.final.source.palette.family) (small : q.1≤8) (bad : ¬C.Predicate G q) :
    (∃d : OI.K G,d≠0 ∧ Gadget.Realizes run.final.source.palette.family .disequality
      (d • GlobalCloseCompletionKleinH6RMBell.core)) ∨
    Nonempty (T.Step G run.final.source.palette run.final.ready.torsion) := by
  let P := run.final.source.palette
  obtain ⟨i,hi⟩ := retained
  obtain ⟨N⟩ := C.exists_minimum G P ⟨i,fun h=>bad (hi ▸ h)⟩
  have smallN : N.signature.1≤8 :=
    (N.arity_le_retained G P (C.Predicate G) (C.split_closed G) q ⟨i,hi⟩ bad).trans small
  rcases higher with ⟨cardinal,noncyclic,standard,m,f,proper,even,high,core,literal,stable⟩
  have prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)) := by simpa only [literal] using core.prime
  have mem : (⟨m+2,f⟩ : AnySignature (OI.K G))∈P.family := by simpa only [literal] using core.retained
  have actual := Gadget.realizes_of_mem P.family .disequality f mem
  have upper := GlobalCloseCompletionKleinHigherNonaffineCurrent.stable_prime_arity_le_eight
    G P run.final.ready.torsion cardinal noncyclic standard f even prime stable
  have cases : m=4 ∨ m=6 := by obtain ⟨k,hk⟩ := even;omega
  have exit4 (q4 : Signature (OI.K G) 4) (actual4 : Gadget.Realizes P.family .disequality q4)
      (nonmatching : ¬MatchingOrZero (actualTransfers P.family) q4) :
      Nonempty (T.Step G P run.final.ready.torsion) :=
    PaperControlled.EngineKleinTransitions.restart_step G P run.final.ready.torsion
      cardinal noncyclic ⟨q4,actual4,nonmatching⟩
  rcases cases with rfl|rfl
  · obtain ⟨c,hc,r,normal⟩ := GlobalCloseCompletionKleinStandardRealLine.current_realLine
      G P run.final.ready.torsion cardinal noncyclic standard (n:=4) f (by decide) stable
    rcases GlobalCloseCompletionKleinSixOriginal.source G P run.final.ready.torsion cardinal noncyclic standard
      f prime ⟨1,one_ne_zero,by simpa using actual⟩ r c hc normal with h6|quaternary
    · exact Or.inl h6
    · obtain ⟨q4,_live,actual4,nonmatching⟩ := quaternary
      exact Or.inr (exit4 q4 actual4 nonmatching)
  · have domain := GlobalCloseCompletionKleinHigherNonaffinePredicateBounds.noncharacter_prime_domain
      G P run.final.ready.noUnary run.final.ready.noOdd run.final.ready.torsion cardinal noncyclic standard
      N.signature N.retained N.prime N.bad
    have lower := core.minimum N.signature N.retained N.prime (by omega)
    have coreSize : core.signature.1=8 := congrArg Sigma.fst literal
    have size : N.signature.1=8 := by omega
    let selected : MinimumCore P.family :=
      {signature:=N.signature,retained:=N.retained,prime:=N.prime,nonbinary:=by omega,
       minimum:=fun g hg hp hn=>by have h:=core.minimum g hg hp hn;omega}
    obtain ⟨t,g,_proper,_even,exactG,deck⟩ := GroupPreparedStability.forExhausted G base run noPrior selected
    have st : t=6 := by have h:=congrArg Sigma.fst exactG;change N.signature.1=t+2 at h;omega
    subst t
    have primeG : Prime (⟨8,g⟩ : AnySignature (OI.K G)) := by simpa only [exactG] using selected.prime
    have memG : (⟨8,g⟩ : AnySignature (OI.K G))∈P.family := by simpa only [exactG] using selected.retained
    have badG : ¬C.Predicate G ⟨8,g⟩ := by simpa only [←exactG] using N.bad
    rcases GlobalCloseCompletionKleinEightCharacter.stable_character G P run.final.ready.torsion
      cardinal noncyclic standard g primeG (Gadget.realizes_of_mem _ .disequality g memG) deck with flat|quaternary
    · exact (badG flat).elim
    · obtain ⟨q4,_live,actual4,nonmatching⟩ := quaternary
      exact Or.inr (exit4 q4 actual4 nonmatching)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinH6Prepared
end
