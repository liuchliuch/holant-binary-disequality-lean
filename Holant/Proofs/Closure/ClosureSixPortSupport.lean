import Holant.Proofs.Closure.ClosureSixPortParity
import Mathlib.Data.Fin.VecNotation

/-! NEW UNVERIFIED literal normalized six-to-four support table. This is the
48-case Boolean core of corrected-paper Proposition cert-nd-q6-support-lowering.
It does not assume or assert that a general tensor already has this form. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant

def firstFlat (z w : Bool) : Word 6 := ![z,z,w,w,z,z]

def secondFlat (edge : Fin 6) (a b o z w : Bool) : Word 6 :=
  match edge.val with
  | 0 => ![z,!z,w,w^^a,o^^z,(o^^z)^^b]
  | 1 => ![z,!z,w,o^^z,w^^a,(o^^z)^^b]
  | 2 => ![z,!z,w,o^^z,(o^^z)^^b,w^^a]
  | 3 => ![z,!z,o^^z,w,w^^a,(o^^z)^^b]
  | 4 => ![z,!z,o^^z,w,(o^^z)^^b,w^^a]
  | _ => ![z,!z,o^^z,(o^^z)^^b,w,w^^a]

def flatWord (edge : Fin 6) (a b o sector z w : Bool) : Word 6 :=
  if sector then secondFlat edge a b o z w else firstFlat z w

def flatSupport (edge : Fin 6) (a b o : Bool) : Finset (Word 6) :=
  Finset.univ.image (fun v : Bool×Bool×Bool => flatWord edge a b o v.1 v.2.1 v.2.2)

def projectionWitness (edge : Fin 6) (a b o : Bool) : Fin 6 × Fin 6 × Bool :=
  match edge.val,a,b,o with
  | 0,false,false,false => (0,4,false)
  | 0,false,false,true => (1,4,false)
  | 0,false,true,_ => (0,0,false)
  | 0,true,false,false => (0,4,false)
  | 0,true,false,true => (1,4,false)
  | 0,true,true,false => (0,4,false)
  | 0,true,true,true => (0,5,false)
  | 1,false,false,false => (0,5,false)
  | 1,false,false,true => (1,5,false)
  | 1,false,true,false => (1,3,true)
  | 1,false,true,true => (0,3,true)
  | 1,true,false,false => (0,3,false)
  | 1,true,false,true => (1,3,false)
  | 1,true,true,false => (1,5,false)
  | 1,true,true,true => (0,5,false)
  | 2,false,false,false => (0,4,false)
  | 2,false,false,true => (1,4,false)
  | 2,false,true,false => (1,3,true)
  | 2,false,true,true => (0,3,true)
  | 2,true,false,false => (0,3,false)
  | 2,true,false,true => (1,3,false)
  | 2,true,true,false => (1,4,false)
  | 2,true,true,true => (0,4,false)
  | 3,false,false,false => (0,5,false)
  | 3,false,false,true => (1,5,false)
  | 3,false,true,false => (1,2,true)
  | 3,false,true,true => (0,2,true)
  | 3,true,false,false => (0,2,false)
  | 3,true,false,true => (1,2,false)
  | 3,true,true,false => (1,5,false)
  | 3,true,true,true => (0,5,false)
  | 4,false,false,false => (0,4,false)
  | 4,false,false,true => (1,4,false)
  | 4,false,true,false => (1,2,true)
  | 4,false,true,true => (0,2,true)
  | 4,true,false,false => (0,2,false)
  | 4,true,false,true => (1,2,false)
  | 4,true,true,false => (1,4,false)
  | 4,true,true,true => (0,4,false)
  | _,false,false,false => (0,2,false)
  | _,false,false,true => (0,2,true)
  | _,false,true,_ => (0,4,false)
  | _,true,_,false => (0,2,false)
  | _,true,_,true => (0,2,true)

def selectedSupport (edge : Fin 6) (a b o : Bool) : Finset (Word 6) :=
  (flatSupport edge a b o).filter (fun x =>
    (x (projectionWitness edge a b o).1 ^^ x (projectionWitness edge a b o).2.1) =
      (projectionWitness edge a b o).2.2)

abbrev FlatProjectionInjective (edge : Fin 6) (a b o : Bool) : Prop :=
  let key := projectionWitness edge a b o
  ∀ s z w s' z' w' : Bool,
    let x := flatWord edge a b o s z w
    let y := flatWord edge a b o s' z' w'
    (x key.1 ^^ x key.2.1) = key.2.2 →
    (y key.1 ^^ y key.2.1) = key.2.2 →
    (∀ r : Fin 6, r ≠ key.1 → r ≠ key.2.1 → x r = y r) → x = y

instance flatProjectionDecidable (edge : Fin 6) (a b o : Bool) :
    Decidable (FlatProjectionInjective edge a b o) := by
  unfold FlatProjectionInjective
  infer_instance

def nativeMatchingSupport (o : Bool) : Finset (Word 6) :=
  Finset.univ.filter (fun x : Word 6 =>
    x 0 = x (if o then 5 else 4) ∧
    x 1 = x (if o then 4 else 5) ∧ x 2 = x 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The two exceptional normalized entries are exactly literal three-edge
matching cosets; every other entry has an injective six/eight-word projection. -/
theorem canonical_four_flat_atlas (edge : Fin 6) (a b o : Bool) :
    (edge=0 ∧ a=false ∧ b=true ∧ flatSupport edge a b o = nativeMatchingSupport o) ∨
    ((projectionWitness edge a b o).1 ≠ (projectionWitness edge a b o).2.1 ∧
      FlatProjectionInjective edge a b o ∧
      ((selectedSupport edge a b o).card=6 ∨ (selectedSupport edge a b o).card=8)) := by
  fin_cases edge <;> cases a <;> cases b <;> cases o <;> decide

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
