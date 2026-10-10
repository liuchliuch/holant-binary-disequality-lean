import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionCore
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedPins

/-! Choose the odd orientation by renaming actual port groups. The private
and exposed variables are kept separate throughout the emitted recipe. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalMixedProjectionPorts
open Holant
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXSeparateSignedProjection (signedCount rowPort)
end P
namespace C
export NoXReciprocalMixedProjectionCore (selected logical)
end C
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {n m : ℕ}
def oriented (p : Fin n→Port m) (sign : Fin m→Bool) (i : Fin n) : Port m :=
  match p i with
  | .inl b=>.inl b
  | .inr (j,b)=>.inr (j,b ^^ sign j)

theorem count (p : Fin n→Port m) (sign : Fin m→Bool) (j : Fin m) (bit : Bool) :
    P.signedCount (oriented p sign) j bit=P.signedCount p j (bit ^^ sign j) := by
  unfold P.signedCount
  apply Finset.sum_congr rfl
  intro i _
  cases hi:p i with
  | inl b=>simp [oriented,hi]
  | inr q=>
    rcases q with ⟨k,b⟩
    by_cases hk:k=j
    · subst k
      cases hb:b <;> cases hs:sign j <;> cases bit <;> simp [oriented,hi,hb,hs]
    · simp [oriented,hi,hk]

theorem selected_word (p : Fin n→Port m) (sign z y : Fin m→Bool) :
    T.substitute (P.rowPort (oriented p sign)) (Fin.addCases z y)=C.selected p sign z y := by
  funext i
  cases hi:p i with
  | inl b=>simp [T.substitute,P.rowPort,oriented,C.selected,hi]
  | inr q=>
    rcases q with ⟨j,b⟩
    cases hb:b <;> cases hs:sign j <;>
      simp only [T.substitute,P.rowPort,oriented,C.selected,hi,hb,hs,Bool.false_xor,Bool.true_xor,
        Bool.not_false,Bool.not_true,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false,
        Sum.elim_inr,Fin.addCases_left,Fin.addCases_right]

theorem logical_word (p : Fin n→Port m) (sign z : Fin m→Bool) :
    word (oriented p sign) z=word p (C.logical sign z) := by
  funext i
  cases hi:p i with
  | inl b=>simp [word,oriented,hi]
  | inr q=>
    rcases q with ⟨j,b⟩
    simp [word,oriented,C.logical,hi,Bool.xor_assoc]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalMixedProjectionPorts
end
