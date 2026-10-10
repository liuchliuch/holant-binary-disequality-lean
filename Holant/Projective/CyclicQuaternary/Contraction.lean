import Holant.Projective.CyclicQuaternary.Family

/-! Literal finite-sum phase contractions of an even four-port Walsh table.
Ports keep their original positions; Fin3 indexes {01,02,03}, the side bit
selects that pair or its complement, and the order bit swaps the residual ports.
The right factor Z is the transfer convention, not an additional gadget. -/
noncomputable section
namespace Holant.Projective.CyclicQuaternary
open CyclicPhasePencil
variable {K : Type*} [Field K]
abbrev Word := Fin 4 → Bool

def odd (w : Word) : Bool := Bool.xor (Bool.xor (Bool.xor (w 0) (w 1)) (w 2)) (w 3)
def weight (w : Word) : ℕ := ∑ i : Fin 4, if w i then 1 else 0
def EvenSupported (q : Signature K 4) : Prop := ∀ w, odd w=true → q w=0

theorem odd_false_iff_even (w : Word) : odd w=false ↔ Even (weight w) := by
  simp only [weight,Fin.sum_univ_succ]
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    norm_num [odd,h0,h1,h2,h3] <;> decide

theorem evenSupported_iff (q : Signature K 4) :
    EvenSupported q ↔ ∀ w, ¬Even (weight w) → q w=0 := by
  constructor
  · intro h w hw
    apply h w
    cases hp : odd w
    · exact (hw ((odd_false_iff_even w).mp hp)).elim
    · rfl
  · intro h w hw
    apply h w
    intro he
    have hf := (odd_false_iff_even w).mpr he
    rw [hw] at hf
    contradiction

/-- Original port placement of deleted bits a,b and residual bits u,v. -/
def join (i : Fin 3) (side a b u v : Bool) : Word :=
  if side then
    if i=0 then ![u,v,a,b] else if i=1 then ![u,a,v,b] else ![u,a,b,v]
  else
    if i=0 then ![a,b,u,v] else if i=1 then ![a,u,b,v] else ![a,u,v,b]

def endpoint0 (q : Signature K 4) : K := q ![false,false,false,false]
def endpoint1 (q : Signature K 4) : K := q ![true,true,true,true]
def coordinates (q : Signature K 4) : Blocks K := fun i =>
  (q (join i false true true false false),q (join i false false false true true))

def firstCoordinate (xs : Blocks K) (i : Fin 3) (side : Bool) : K :=
  if side then (xs i).2 else (xs i).1
def secondCoordinate (xs : Blocks K) (i : Fin 3) (side : Bool) : K :=
  if side then (xs i).1 else (xs i).2

/-- The actual normalized bilinear contraction with diag(1,-s). -/
def contraction (q : Signature K 4) (i : Fin 3) (side : Bool) (s : K) : Kernel K :=
  fun u v => ∑ a : Bool, ∑ b : Bool, diagonal 1 (-s) a b * q (join i side a b u v)

/-- Its ordinary first-two-port Signature.contract expression after the
explicit original-port rearrangement. This is an equality of finite sums. -/
theorem contraction_eq_signature_contract (q : Signature K 4) (i : Fin 3)
    (side : Bool) (s : K) (u v : Bool) :
    contraction q i side s u v =
      Signature.contract (diagonal 1 (-s))
        (fun w : Word => q (join i side (w 0) (w 1) (w 2) (w 3))) ![u,v] := rfl

theorem contraction_two_terms (q : Signature K 4) (i : Fin 3)
    (side : Bool) (s : K) (u v : Bool) :
    contraction q i side s u v = q (join i side false false u v)-s*q (join i side true true u v) := by
  simp [contraction,diagonal,sub_eq_add_neg,add_comm]

theorem odd_join_diagonal (i : Fin 3) (side a u v : Bool) :
    odd (join i side a a u v)=Bool.xor u v := by
  fin_cases i <;> cases side <;> cases a <;> cases u <;> cases v <;> rfl

theorem contraction_diagonal (q : Signature K 4) (heven : EvenSupported q)
    (i : Fin 3) (side : Bool) (s : K) :
    contraction q i side s = diagonal
      (endpoint0 q-s*firstCoordinate (coordinates q) i side)
      (secondCoordinate (coordinates q) i side-s*endpoint1 q) := by
  funext u v
  rw [contraction_two_terms]
  cases u <;> cases v
  · fin_cases i <;> cases side <;> rfl
  · have h0 := heven (join i side false false false true) (by rw [odd_join_diagonal]; rfl)
    have h1 := heven (join i side true true false true) (by rw [odd_join_diagonal]; rfl)
    simp [h0,h1,diagonal]
  · have h0 := heven (join i side false false true false) (by rw [odd_join_diagonal]; rfl)
    have h1 := heven (join i side true true true false) (by rw [odd_join_diagonal]; rfl)
    simp [h0,h1,diagonal]
  · fin_cases i <;> cases side <;> rfl

/-- Both orders of the residual ports give the same actual diagonal card. -/
def orderedContraction (q : Signature K 4) (i : Fin 3) (side order : Bool) (s : K) : Kernel K :=
  if order then Kernel.transpose (contraction q i side s) else contraction q i side s

theorem orderedContraction_eq (q : Signature K 4) (heven : EvenSupported q)
    (i : Fin 3) (side order : Bool) (s : K) :
    orderedContraction q i side order s=contraction q i side s := by
  cases order
  · rfl
  · change Kernel.transpose (contraction q i side s)=contraction q i side s
    rw [contraction_diagonal q heven]
    funext u v
    cases u <;> cases v <;> rfl

/-- Transfer cards explicitly include the source's right factor Z. -/
def transferCard (q : Signature K 4) (i : Fin 3) (side order : Bool) (s : K) : Kernel K :=
  Kernel.mul (orderedContraction q i side order s) Z

theorem transferCard_eq (q : Signature K 4) (heven : EvenSupported q)
    (i : Fin 3) (side order : Bool) (s : K) :
    transferCard q i side order s=card (endpoint0 q)
      (firstCoordinate (coordinates q) i side) (secondCoordinate (coordinates q) i side) (endpoint1 q) s := by
  rw [transferCard,orderedContraction_eq q heven,contraction_diagonal q heven]
  rfl

def AllPhaseCards (m : ℕ) (q : Signature K 4) : Prop :=
  ∀ (i : Fin 3) (side order : Bool) (s : K), s^m=1 →
    transferCard q i side order s=0 ∨ IsPhase m (transferCard q i side order s)

theorem allPhaseCards_iff (m : ℕ) (q : Signature K 4) (heven : EvenSupported q) :
    AllPhaseCards m q ↔ PhaseFamilies m (endpoint0 q) (endpoint1 q) (coordinates q) := by
  constructor
  · intro h i
    exact ⟨fun s hs => by simpa [transferCard_eq q heven,firstCoordinate,secondCoordinate] using h i false false s hs,
      fun s hs => by simpa [transferCard_eq q heven,firstCoordinate,secondCoordinate] using h i true false s hs⟩
  · intro h i side order s hs
    rw [transferCard_eq q heven]
    cases side
    · exact (h i).1 s hs
    · exact (h i).2 s hs

end Holant.Projective.CyclicQuaternary
