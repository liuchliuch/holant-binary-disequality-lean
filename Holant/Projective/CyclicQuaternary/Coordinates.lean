import Holant.Projective.CyclicQuaternary.Classification

/-! All eight literal even Walsh coefficients, with the source complement order.
The encoder is inverse to coordinate extraction on every even-supported table. -/
noncomputable section
namespace Holant.Projective.CyclicQuaternary
variable {K : Type*} [Field K]

def ofCoordinates (p t : K) (xs : Blocks K) : Signature K 4 := fun w =>
  match w 0,w 1,w 2,w 3 with
  | false,false,false,false => p
  | true,true,true,true => t
  | true,true,false,false => (xs 0).1
  | false,false,true,true => (xs 0).2
  | true,false,true,false => (xs 1).1
  | false,true,false,true => (xs 1).2
  | true,false,false,true => (xs 2).1
  | false,true,true,false => (xs 2).2
  | _,_,_,_ => 0

theorem ofCoordinates_even (p t : K) (xs : Blocks K) : EvenSupported (ofCoordinates p t xs) := by
  intro w hw
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp_all [odd,ofCoordinates]

@[simp] theorem endpoint0_ofCoordinates (p t : K) (xs : Blocks K) : endpoint0 (ofCoordinates p t xs)=p := rfl
@[simp] theorem endpoint1_ofCoordinates (p t : K) (xs : Blocks K) : endpoint1 (ofCoordinates p t xs)=t := rfl
@[simp] theorem coordinates_ofCoordinates (p t : K) (xs : Blocks K) : coordinates (ofCoordinates p t xs)=xs := by
  funext i
  fin_cases i <;> rfl

/-- No even Walsh coefficient is omitted by the endpoint/complement table. -/
theorem ofCoordinates_extract (q : Signature K 4) (heven : EvenSupported q) :
    ofCoordinates (endpoint0 q) (endpoint1 q) (coordinates q)=q := by
  funext w
  have hw : w=![w 0,w 1,w 2,w 3] := by funext i; fin_cases i <;> rfl
  conv_rhs => rw [hw]
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp only [ofCoordinates,h0,h1,h2,h3]
  all_goals first
    | rfl
    | (symm; apply heven; rfl)

end Holant.Projective.CyclicQuaternary
