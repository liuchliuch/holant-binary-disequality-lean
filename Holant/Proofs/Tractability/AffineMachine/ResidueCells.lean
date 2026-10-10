import Holant.Proofs.Tractability.AffineMachine.WireLists
import Holant.Proofs.Tractability.AffineMachine.FiniteCore


namespace Holant.LocalDrafts.Tractability.AffineMachine.ResidueCells

open Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open UniversalPairReduction.SmoothingCompiler

def encode4 (q : ZMod 4) : List Bool := [decide (q.val % 2 = 1), decide (q.val / 2 = 1)]
def decode4 : List Bool → Option (ZMod 4)
  | [a, b] => some ((if a then 1 else 0) + (if b then 2 else 0))
  | _ => none

def encoding4 : Encoding (ZMod 4) Bool where
  encode := encode4
  decode := decode4
  decode_encode q := by fin_cases q <;> decide

@[simp] theorem encoding4_length (q : ZMod 4) : (encoding4.encode q).length = 2 := rfl

noncomputable def unary4 {A : Type} (ea : Encoding A Bool) (f : ZMod 4 → A) : Computes encoding4 ea f :=
  FiniteRecode.computes encoding4 ea f 2 (fun _ => le_rfl)

noncomputable def binary4 (f : ZMod 4 → ZMod 4 → ZMod 4) :
    Computes (pairEncoding encoding4 encoding4) encoding4 (fun x => f x.1 x.2) :=
  FiniteRecode.computes _ _ _ 7 (fun x => by simp [pairEncoding_length])

noncomputable def add4 := binary4 (· + ·)
noncomputable def sub4 := binary4 (· - ·)
noncomputable def mul4 := binary4 (· * ·)

noncomputable def test4 (p : ZMod 4 → Bool) : Computes encoding4 encodingBoolBool p := unary4 _ p

noncomputable def bool4 : Computes encodingBoolBool encoding4 FiniteCore.bit4 :=
  FiniteRecode.computes _ _ _ 1 (fun b => by cases b <;> rfl)

noncomputable def xor : Computes (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun x => Bool.xor x.1 x.2) := ProductMachine.Rewrite.boolPairComputes (fun x => Bool.xor x.1 x.2)

noncomputable def sum4 : Computes (framedListEncoding encoding4) encoding4 List.sum := by
  have h (xs : List (ZMod 4)) (q : ZMod 4) : xs.foldl (· + ·) q = q + xs.sum := by
    induction xs generalizing q <;> simp_all [add_assoc]
  exact congrComputes (FiniteFold.computes encoding4 encoding4 2 (· + ·) 0 encoding4_length)
    (fun xs => by simpa using h xs 0)

def parity (xs : List Bool) : Bool := xs.foldl Bool.xor false
noncomputable def parityComputes : Computes (framedListEncoding encodingBoolBool) encodingBoolBool parity :=
  FiniteFold.computes encodingBoolBool encodingBoolBool 1 Bool.xor false (fun b => by cases b <;> rfl)

noncomputable def all : Computes (framedListEncoding encodingBoolBool) encodingBoolBool
    (fun xs => xs.all id) := by
  have h (xs : List Bool) (b : Bool) : xs.foldl Bool.and b = (b && xs.all id) := by
    induction xs generalizing b with
    | nil => cases b <;> rfl
    | cons x xs ih => simp only [List.foldl_cons, List.all_cons, ih]; cases b <;> cases x <;> simp
  exact congrComputes (FiniteFold.computes encodingBoolBool encodingBoolBool 1 Bool.and true
    (fun b => by cases b <;> rfl)) (fun xs => by simpa using h xs true)

noncomputable def any : Computes (framedListEncoding encodingBoolBool) encodingBoolBool
    (fun xs => xs.any id) := by
  have h (xs : List Bool) (b : Bool) : xs.foldl Bool.or b = (b || xs.any id) := by
    induction xs generalizing b with
    | nil => cases b <;> rfl
    | cons x xs ih => simp only [List.foldl_cons, List.any_cons, ih]; cases b <;> cases x <;> simp
  exact congrComputes (FiniteFold.computes encodingBoolBool encodingBoolBool 1 Bool.or false
    (fun b => by cases b <;> rfl)) (fun xs => by simpa using h xs false)

theorem parity_value (xs : List Bool) :
    FiniteCore.bit2 (parity xs) = (xs.map FiniteCore.bit2).sum := by
  have h (xs : List Bool) (b : Bool) : FiniteCore.bit2 (xs.foldl Bool.xor b) =
      FiniteCore.bit2 b + (xs.map FiniteCore.bit2).sum := by
    induction xs generalizing b with
    | nil => simp
    | cons x xs ih =>
      rw [List.foldl_cons, ih]
      have hx : FiniteCore.bit2 (Bool.xor b x) = FiniteCore.bit2 b + FiniteCore.bit2 x := by
        cases b <;> cases x <;> decide
      simp [hx, add_assoc]
  change FiniteCore.bit2 (xs.foldl Bool.xor false) = _
  calc
    _ = FiniteCore.bit2 false + (xs.map FiniteCore.bit2).sum := h xs false
    _ = _ := zero_add _

end Holant.LocalDrafts.Tractability.AffineMachine.ResidueCells
