import Holant.Certificates.FourthRootOdd.PhaseData

/-! The512 literal affine odd states from the source parametrization. Signs
are actual ±1 fourth roots, and every original coefficient label is retained. -/
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops

abbrev FamilyParameters := AState × Bool × Bool × Bool

def familyState (p : FamilyParameters) : State :=
  let A := p.1.1
  let B := p.1.2.1
  let C := p.1.2.2
  let x := signPhase p.2.1
  let y := signPhase p.2.2.1
  let z := signPhase p.2.2.2
  (p.1,(x+y+z+A+B+C,z+B+C,y+A+C,x+A+B))

def shiftState (s : State) (δ : Fin 4) : State :=
  (s.1,(s.2.1+δ,s.2.2.1+δ,s.2.2.2.1+δ,s.2.2.2.2+δ))

def recoverFamily (s : State) (δ : Fin 4) : FamilyParameters :=
  (s.1,decide (s.2.2.2.2+δ-s.1.1-s.1.2.1=2),
    decide (s.2.2.2.1+δ-s.1.1-s.1.2.2=2),
    decide (s.2.2.1+δ-s.1.2.1-s.1.2.2=2))

set_option maxRecDepth 200000 in
theorem recover_familyState : ∀ p : FamilyParameters, recoverFamily (familyState p) 0=p := by decide

theorem familyState_injective : Function.Injective familyState := by
  intro p q h
  have hh := congrArg (fun s => recoverFamily s 0) h
  simpa only [recover_familyState] using hh

theorem affine_family_count : ((Finset.univ : Finset FamilyParameters).image familyState).card=512 := by
  rw [Finset.card_image_of_injective _ familyState_injective]
  simp [FamilyParameters,AState]

theorem phaseCode_add : ∀ i j : Fin 4,
    (((i+j).val : ℕ) : ZMod 4)=(i.val : ZMod 4)+(j.val : ZMod 4) := by decide

theorem alpha_shift (s : State) (δ : Fin 4) : alpha (shiftState s δ)=alpha s := rfl
theorem beta_shift (s : State) (δ : Fin 4) (j : Fin 4) : beta (shiftState s δ) j=beta s j+δ := by
  fin_cases j <;> rfl

end Holant.Certificates.FourthRootOdd
