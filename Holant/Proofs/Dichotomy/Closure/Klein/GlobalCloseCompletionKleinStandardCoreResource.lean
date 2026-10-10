import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixOriginal
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMOriginal

/-! The complete standard-Pauli stable-prime resource source. The proved
higher-arity exclusion and the genuine six/eight sources leave an actual RM8
resource or an actual original-field nonmatching quaternary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardCoreResource
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem source {m : ℕ} (f : Signature (OI.K G) (m+2)) (higher : 6≤m+2) (even : Even (m+2))
    (prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G))) (actual : Gadget.Realizes P.family .disequality f)
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    (∃d : OI.K G,d≠0 ∧ Gadget.Realizes P.family .disequality (d • GlobalCloseCompletionC2RMActual.rm)) ∨
    ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
      ¬MatchingOrZero (actualTransfers P.family) q := by
  have bound := GlobalCloseCompletionKleinHigherNonaffineCurrent.stable_prime_arity_le_eight
    G P torsion cardinal noncyclic standard f even prime stable
  have cases : m=4 ∨ m=6 := by obtain ⟨k,hk⟩ := even;omega
  rcases cases with rfl|rfl
  · obtain ⟨c,hc,r,normal⟩ := GlobalCloseCompletionKleinStandardRealLine.current_realLine
      G P torsion cardinal noncyclic standard (n:=4) f (by decide) stable
    exact GlobalCloseCompletionKleinSixOriginal.rm_source G P torsion cardinal noncyclic standard
      f prime ⟨1,one_ne_zero,by simpa using actual⟩ r c hc normal
  · exact GlobalCloseCompletionKleinEightRMOriginal.stable_source
      G P torsion cardinal noncyclic standard f prime actual stable

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardCoreResource
end
