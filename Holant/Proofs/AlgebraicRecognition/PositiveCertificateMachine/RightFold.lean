import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.Codec


namespace Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.RightFold
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.Tractability.ProductMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
variable {C A B : Type} (ec : Encoding C Bool) (ea : Encoding A Bool) (eb : Encoding B Bool)
variable (f : C → A → B → B) (default : A)

abbrev State := C × (List A × (ℕ × B))
def stateEncoding := pairEncoding ec (pairEncoding (framedListEncoding ea) (pairEncoding encodingNatBool eb))
def inputEncoding := pairEncoding ec (pairEncoding (framedListEncoding ea) eb)
def start (x : C × (List A × B)) : State (C := C) (A := A) (B := B) :=
  (x.1,x.2.1,x.2.1.length,x.2.2)
def step (s : State (C := C) (A := A) (B := B)) : State (C := C) (A := A) (B := B) :=
  (s.1,s.2.1,s.2.2.1-1,f s.1 (s.2.1.getD (s.2.2.1-1) default) s.2.2.2)

theorem drop_cons (xs : List A) (j : ℕ) (h : j < xs.length) :
    xs.drop j = xs.getD j default :: xs.drop (j+1) := by
  induction xs generalizing j with
  | nil => simp at h
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j => simpa using ih j (by simpa using h)

theorem iterate_start (c : C) (xs : List A) (b : B) (i : ℕ) (hi : i ≤ xs.length) :
    ((step f default)^[i]) (start (c,xs,b)) =
      (c,xs,xs.length-i,(xs.drop (xs.length-i)).foldr (f c) b) := by
  revert hi
  induction i with
  | zero => intro hi; simp [start]
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply',ih (by omega)]
    have hj : xs.length-(i+1)+1=xs.length-i := by omega
    have hsub : xs.length-i-1=xs.length-(i+1) := by omega
    rw [drop_cons default xs (xs.length-(i+1)) (by omega),List.foldr_cons,hj]
    simp only [step,hsub]

noncomputable section
def binaryToUnary : Executes encodingNatBool UnaryBinary.unaryEncoding id :=
  let w := ComplexIsolation.RootSearchDriver.Height.binaryToUnary
  ⟨w.machine,fun n => w.time (encodingNatBool.encode n).length,w.outputs⟩

def body (w : Executes (pairEncoding ec (pairEncoding ea eb)) eb (fun x => f x.1 x.2.1 x.2.2)) :
    Executes (stateEncoding ec ea eb) (stateEncoding ec ea eb) (step f default) := by
  let c := Wiring.firstComputes ec (pairEncoding (framedListEncoding ea) (pairEncoding encodingNatBool eb))
  let tail := Wiring.secondComputes ec (pairEncoding (framedListEncoding ea) (pairEncoding encodingNatBool eb))
  let xs := tail.andThen (Wiring.firstComputes (framedListEncoding ea) (pairEncoding encodingNatBool eb))
  let rest := tail.andThen (Wiring.secondComputes (framedListEncoding ea) (pairEncoding encodingNatBool eb))
  let index := (rest.andThen (Wiring.firstComputes encodingNatBool eb)).andThen Rewrite.predComputes
  let acc := rest.andThen (Wiring.secondComputes encodingNatBool eb)
  let unary := (Executes.ofComputes index).comp binaryToUnary
  let item := ((Executes.ofComputes xs).pair unary).comp (Executes.ofComputes (WireLists.getD ea default))
  let next := ((Executes.ofComputes c).pair (item.pair (Executes.ofComputes acc))).comp w
  exact (Executes.ofComputes c).pair ((Executes.ofComputes xs).pair ((Executes.ofComputes index).pair next))

def executes (w : Executes (pairEncoding ec (pairEncoding ea eb)) eb (fun x => f x.1 x.2.1 x.2.2)) :
    Executes (inputEncoding ec ea eb) eb (fun x => x.2.1.foldr (f x.1) x.2.2) := by
  let c := Wiring.firstComputes ec (pairEncoding (framedListEncoding ea) eb)
  let tail := Wiring.secondComputes ec (pairEncoding (framedListEncoding ea) eb)
  let xs := tail.andThen (Wiring.firstComputes (framedListEncoding ea) eb)
  let b := tail.andThen (Wiring.secondComputes (framedListEncoding ea) eb)
  let n := (xs.andThen (WireLists.lengthComputes ea)).andThen UnaryBinary.computes
  let prepare := Executes.ofComputes (pairComputes n (pairComputes c (pairComputes xs (pairComputes n b))))
  let loop := Iteration.executes (stateEncoding ec ea eb) (body ec ea eb f default w)
  let extract := Executes.ofComputes
    (((Wiring.secondComputes ec (pairEncoding (framedListEncoding ea) (pairEncoding encodingNatBool eb))).andThen
      (Wiring.secondComputes (framedListEncoding ea) (pairEncoding encodingNatBool eb))).andThen
        (Wiring.secondComputes encodingNatBool eb))
  exact ((prepare.comp loop).comp extract).congr (fun x => by
    change (((step f default)^[x.2.1.length]) (start x)).2.2.2 = _
    have h := iterate_start f default x.1 x.2.1 x.2.2 x.2.1.length (le_refl _)
    simpa only [start,Nat.sub_self,List.drop_zero] using congrArg (fun s => s.2.2.2) h)
end
end Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.RightFold
