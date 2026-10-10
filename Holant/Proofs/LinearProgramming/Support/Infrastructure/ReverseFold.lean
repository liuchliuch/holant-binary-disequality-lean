import Holant.Proofs.LinearProgramming.Support.Infrastructure.Iterate
import Holant.Proofs.LinearProgramming.Support.MachineCombinators

/-!
Physical reverse-index fold. The unary cursor, list and accumulator are tape
words. Even the final padded rounds pay for the computed, then discarded,
candidate. This helper gives finite execution only; it does not infer a
polynomial bound by iterating a polynomial one-step bound.
-/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.ReverseFold
open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators

open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure


variable {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
  (default : A) (f : A → B → B)

abbrev State := List A × (ℕ × B)
def tailEncoding := pairEncoding UnaryBinary.unaryEncoding eb
def encoding := pairEncoding (framedListEncoding ea) (tailEncoding eb)
def inputEncoding := pairEncoding (framedListEncoding ea) eb
def start (q : List A × B) : State (A := A) (B := B) := (q.1,q.1.length,q.2)
def step (s : State (A := A) (B := B)) : State (A := A) (B := B) :=
  if s.2.1=0 then s else
    (s.1,s.2.1-1,f (s.1.getD (s.2.1-1) default) s.2.2)

theorem take_succ (xs : List A) (k : ℕ) (hk : k<xs.length) :
    xs.take (k+1)=xs.take k++[xs.getD k default] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simpa using congrArg (x::·) (ih k (by simpa using hk))

theorem iterate_count (xs : List A) (k : ℕ) (b : B) (hk : k≤xs.length) :
    ((step default f)^[k]) (xs,k,b) = (xs,0,(xs.take k).foldr f b) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    simp only [step, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih _ (by omega),take_succ default xs k (by omega),List.foldr_append]
    rfl

theorem stopped (xs : List A) (b : B) (k : ℕ) :
    ((step default f)^[k]) (xs,0,b)=(xs,0,b) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [Function.iterate_succ_apply,step] using ih

theorem drop_cons (xs : List A) (k : ℕ) (hk : k<xs.length) :
    xs.drop k=xs.getD k default::xs.drop (k+1) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons a xs ih =>
    cases k with
    | zero => rfl
    | succ k => simpa using ih k (by simpa using hk)

/-- Exact intermediate state, including every padded round after the cursor
reaches zero. This is the operational link for semantic register-size bounds. -/
theorem iterate_start (q : List A × B) (k : ℕ) :
    ((step default f)^[k]) (start q)=
      (q.1,q.1.length-k,(q.1.drop (q.1.length-k)).foldr f q.2) := by
  induction k with
  | zero => simp [start]
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    by_cases hk : k<q.1.length
    · have hn : q.1.length-k≠0 := by omega
      have he : q.1.length-k-1=q.1.length-(k+1) := by omega
      have hs : q.1.length-(k+1)+1=q.1.length-k := by omega
      have hd := drop_cons default q.1 (q.1.length-(k+1)) (by omega)
      rw [hs] at hd
      simp only [step,if_neg hn,he]
      rw [hd,List.foldr_cons]
    · have h0 : q.1.length-k=0 := by omega
      have h1 : q.1.length-(k+1)=0 := by omega
      simp only [h0,h1,step,ite_true]

theorem byte_iterations (q : List A × B) :
    Iterate.value (encoding ea eb) (step default f) (start q)=
      (q.1,0,q.1.foldr f q.2) := by
  let L := ((encoding ea eb).encode (start q)).length
  have hlen : q.1.length≤L := by
    simp only [L,encoding,tailEncoding,start,pairEncoding_length,
      UnaryBinary.unaryEncoding,List.length_replicate]
    omega
  have hL : L=(L-q.1.length)+q.1.length := by omega
  change ((step default f)^[L]) (q.1,q.1.length,q.2)=_
  rw [hL,Function.iterate_add_apply,iterate_count default f _ _ _ le_rfl]
  simp only [List.take_length]
  exact stopped default f _ _ _

noncomputable section
def list : Computes (encoding ea eb) (framedListEncoding ea)
    (fun s : State (A := A) (B := B) => s.1) := Wiring.firstComputes _ _
def tail := Wiring.secondComputes (framedListEncoding ea) (tailEncoding eb)
def count : Computes (encoding ea eb) UnaryBinary.unaryEncoding
    (fun s : State (A := A) (B := B) => s.2.1) :=
  (tail ea eb).andThen (Wiring.firstComputes _ _)
def acc : Computes (encoding ea eb) eb
    (fun s : State (A := A) (B := B) => s.2.2) :=
  (tail ea eb).andThen (Wiring.secondComputes _ _)

def stepComputes
    (cell : FiniteComputes (pairEncoding ea eb) eb (fun p => f p.1 p.2)) :
    FiniteComputes (encoding ea eb) (encoding ea eb) (step default f) := by
  let prev := (count ea eb).andThen Endpoints.unaryPredecessorComputes
  let entry := AccessPrograms.get ea default (list ea eb) prev
  let updated := (FiniteComputes.ofPoly (pairComputes entry (acc ea eb))).andThen cell
  let candidate := (FiniteComputes.ofPoly (list ea eb)).pair
    ((FiniteComputes.ofPoly prev).pair updated)
  let both := (FiniteComputes.ofPoly (identityComputes (encoding ea eb))).pair candidate
  let old := Wiring.firstComputes (encoding ea eb) (encoding ea eb)
  let new := Wiring.secondComputes (encoding ea eb) (encoding ea eb)
  let done := (pairComputes (old.andThen (count ea eb))
    (constantComputes _ UnaryBinary.unaryEncoding 0)).andThen Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.unaryEqual
  exact (both.andThen (FiniteComputes.ofPoly (ifComputes done old new))).congr
    (fun s => by
      by_cases h : s.2.1=0 <;> simp [step,h])

def startComputes : Computes (inputEncoding ea eb) (encoding ea eb) start :=
  pairComputes (Wiring.firstComputes _ _) (pairComputes
    ((Wiring.firstComputes (framedListEncoding ea) eb).andThen (WireLists.lengthComputes ea))
    (Wiring.secondComputes _ _))

/-- The caller supplies a constructed scalar/row subprogram, not a correctness
oracle. The concrete consumers below instantiate this with rational addition
and the complete physical `put` program. -/
def computes (cell : FiniteComputes (pairEncoding ea eb) eb (fun p => f p.1 p.2)) :
    FiniteComputes (inputEncoding ea eb) eb (fun q => q.1.foldr f q.2) :=
  (((FiniteComputes.ofPoly (startComputes ea eb)).andThen
    (Iterate.computes (encoding ea eb) (step default f)
      (stepComputes ea eb default f cell))).andThen
    (FiniteComputes.ofPoly (acc ea eb))).congr
      (fun q => congrArg (fun s : State (A := A) (B := B) => s.2.2)
        (byte_iterations ea eb default f q))
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.ReverseFold
