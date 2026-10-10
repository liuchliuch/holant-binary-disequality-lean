import Holant.Proofs.Closure.ClosureKleinCurrentExotic
import Holant.Pauli.ExoticKlein.SixPortPhysicalCards
import Holant.Dihedral.TwoCardLocalization.ResidualOrder

/-! The actual CURRENT exotic ordered deck yields the exact original-port
six-port physical safety predicate, preserving zero cards and matching size. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticCards
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Pauli.ExoticKlein
open Holant.Dihedral.TwoCardLocalization (remainingOrder)
open MatchingCard (asMatrix)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem insertPair_fill {P : Type} [DecidableEq P] (u v : P) (hne : u≠v)
    (a b : Bool) (x : Remaining u v→Bool) :
    insertPair u v a b (extendRemaining u v x)=Holant.Pauli.ProjectiveDetermination.fill u v a b x := by
  funext i
  by_cases hi : i=u
  · subst i
    simp [insertPair,Holant.Pauli.ProjectiveDetermination.fill,hne]
  by_cases hj : i=v
  · subst i
    simp [insertPair,Holant.Pauli.ProjectiveDetermination.fill,Ne.symm hne]
  simp [insertPair,extendRemaining,Holant.Pauli.ProjectiveDetermination.fill,hi,hj]

private theorem physical_eq_contract (u v : Fin 6) (hne : u≠v) (a : Label) (h : Signature ℂ 6) :
    SixPort.physicalCard u v a h=contractPair u v (asMatrix (dual a)) h := by
  funext x
  simp only [SixPort.physicalCard,contractPair,insertPair_fill u v hne,asMatrix,Matrix.of_apply]

theorem ordered_physical (h : Signature ℂ 6) (safe : MatchingCard.OrderedPairSafe h) :
    SixPort.AllPhysicalSafe h := by
  have pairSafe := (MatchingCard.pairSafe_iff_ordered h).mpr safe
  intro u v less a
  have card := pairSafe u v (ne_of_lt less) a
  rw [←physical_eq_contract u v (ne_of_lt less) a h] at card
  rcases card with zero|⟨t,M,labels,c,hc,he⟩
  · exact Or.inl zero
  · have portCard : Fintype.card (Remaining u v)=4 := by
      simpa using (Fintype.card_congr (remainingOrder u v (ne_of_lt less))).symm
    have count := M.port_card
    rw [portCard] at count
    have two : t=2 := by omega
    subst t
    exact Or.inr ⟨M,labels,c,hc,he⟩

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (exotic : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.exotic)

include cardinal noncyclic exotic in
theorem current_physical (f : Signature (OI.K G) 6)
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    SixPort.AllPhysicalSafe (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f) :=
  ordered_physical _ (ClosureKleinCurrent.current_exotic_ordered G P torsion cardinal noncyclic exotic f stable)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticCards
end
