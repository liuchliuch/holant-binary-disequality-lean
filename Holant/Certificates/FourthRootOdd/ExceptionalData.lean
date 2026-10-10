import Holant.Certificates.FourthRootOdd.TwoCopy

/-! The exact exceptional64 remaining states and their support-six two-copy
exit. Finite proofs cover all normalized states; the output is the actual
two-native-edge sum through TwoCopy's faithful complex interpretation. -/
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

def signPhase (e : Bool) : Fin 4 := if e then 2 else 0
def exceptionalState (x : AState) (e : Bool) : State :=
  (x,(signPhase e,x.1+signPhase e,x.2.1+signPhase e,x.2.2+signPhase e))
def oddProduct (x : AState) : Prop :=
  x.1+x.2.1+x.2.2=1 ∨ x.1+x.2.1+x.2.2=3
instance (x : AState) : Decidable (oddProduct x) := inferInstanceAs (Decidable (_ ∨ _))
def Exceptional (s : State) : Prop := oddProduct s.1 ∧ ∃ e : Bool, s=exceptionalState s.1 e
instance (s : State) : Decidable (Exceptional s) := inferInstanceAs (Decidable (_ ∧ _))

abbrev Parameters := {x : AState // oddProduct x} × Bool

def parameterState (t : Parameters) : {s : State // Exceptional s} :=
  ⟨exceptionalState t.1.val t.2,t.1.property,⟨t.2,rfl⟩⟩

theorem signPhase_injective : Function.Injective signPhase := by decide

theorem parameterState_injective : Function.Injective parameterState := by
  rintro ⟨x,e⟩ ⟨y,f⟩ h
  have hxy : x.val=y.val := congrArg (fun z => z.val.1) h
  have hef : e=f := signPhase_injective (congrArg (fun z => z.val.2.1) h)
  exact Prod.ext (Subtype.ext hxy) hef

theorem parameterState_surjective : Function.Surjective parameterState := by
  rintro ⟨s,hs⟩
  obtain ⟨e,he⟩ := hs.2
  refine ⟨(⟨s.1,hs.1⟩,e),?_⟩
  apply Subtype.ext
  exact he.symm

theorem exceptional_count : ((Finset.univ : Finset State).filter Exceptional).card=64 := by
  calc
    _ = Fintype.card {s : State // Exceptional s} := (Fintype.card_subtype _).symm
    _ = Fintype.card Parameters :=
      Fintype.card_congr (Equiv.ofBijective parameterState ⟨parameterState_injective,parameterState_surjective⟩).symm
    _ = 64 := by decide

end Holant.Certificates.FourthRootOdd
