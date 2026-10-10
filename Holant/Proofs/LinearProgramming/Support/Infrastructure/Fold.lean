import Holant.Proofs.LinearProgramming.Support.Infrastructure.Iteration
import Holant.Proofs.LinearProgramming.Support.MachineCombinators

/-!
Retiming the old reverse-fold composition tree, with no reassociation or
replacement loop. In particular the candidate branch runs even at cursor zero;
the polynomial step proof pays for it on every padded iteration.
-/
open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.Fold
open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators

open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool) (d : A) (f : A → B → B)
  {cell : FiniteComputes (pairEncoding ea eb) eb (fun p => f p.1 p.2)}

def step (t : Timing cell) : Timing (ReverseFold.stepComputes ea eb d f cell) := by
  let prev := (ReverseFold.count ea eb).andThen Endpoints.unaryPredecessorComputes
  let entry := AccessPrograms.get ea d (ReverseFold.list ea eb) prev
  let updated := (Timing.ofPoly (pairComputes entry (ReverseFold.acc ea eb))).andThen t
  let candidate := (Timing.ofPoly (ReverseFold.list ea eb)).pair ((Timing.ofPoly prev).pair updated)
  let both := (Timing.ofPoly (identityComputes (ReverseFold.encoding ea eb))).pair candidate
  let old := Wiring.firstComputes (ReverseFold.encoding ea eb) (ReverseFold.encoding ea eb)
  let new := Wiring.secondComputes (ReverseFold.encoding ea eb) (ReverseFold.encoding ea eb)
  let done := (pairComputes (old.andThen (ReverseFold.count ea eb))
    (constantComputes _ UnaryBinary.unaryEncoding 0)).andThen Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.unaryEqual
  exact (both.andThen (Timing.ofPoly (ifComputes done old new))).congr (fun s => by
    by_cases h : s.2.1=0 <;> simp [ReverseFold.step,h])

def time (t : Timing cell) (I W : Polynomial ℕ) : Polynomial ℕ :=
  (ReverseFold.startComputes ea eb).time.comp I+2*(W+1)+
    Iteration.total (step ea eb d f t) W+2*(W+1)+(ReverseFold.acc ea eb).time.comp W

/-- The output-word transport in the old fold retains this same run's clock. -/
private theorem output_cast_steps (m : Machine)
    {xs xs' ys ys' : List Bool} {n n' : ℕ}
    (hx : xs=xs') (hy : ys=ys') (hn : n=n')
    (out : Turing.TM2OutputsInTime m.computer xs (some ys) n)
    (h : Turing.TM2OutputsInTime m.computer xs (some ys) n =
      Turing.TM2OutputsInTime m.computer xs' (some ys') n') :
    (Eq.mp h out).steps=out.steps := by
  subst xs'
  subst ys'
  subst n'
  rfl

theorem steps (t : Timing cell) (I W : Polynomial ℕ) (q : List A × B) (N : ℕ)
    (hi : ((ReverseFold.inputEncoding ea eb).encode q).length≤I.eval N)
    (hs : ∀ k,((ReverseFold.encoding ea eb).encode
      (((ReverseFold.step d f)^[k]) (ReverseFold.start q))).length≤W.eval N) :
    ((ReverseFold.computes ea eb d f cell).outputs q).steps≤(time ea eb d f t I W).eval N := by
  let s := ReverseFold.start q
  let v := Iterate.value (ReverseFold.encoding ea eb) (ReverseFold.step d f) s
  have h0 : ((ReverseFold.encoding ea eb).encode s).length≤W.eval N := hs 0
  have hv : ((ReverseFold.encoding ea eb).encode v).length≤W.eval N :=
    hs (((ReverseFold.encoding ea eb).encode s).length)
  have hp := ((ReverseFold.startComputes ea eb).outputs q).steps_le_m.trans
    (natPolynomial_eval_mono (ReverseFold.startComputes ea eb).time hi)
  have hr : ((Iterate.computes (ReverseFold.encoding ea eb) (ReverseFold.step d f)
      (ReverseFold.stepComputes ea eb d f cell)).outputs s).steps ≤
      (Iteration.total (step ea eb d f t) W).eval N :=
    Iteration.steps (step ea eb d f t) W s N hs
  have ha := ((ReverseFold.acc ea eb).outputs v).steps_le_m.trans
    (natPolynomial_eval_mono (ReverseFold.acc ea eb).time hv)
  let run := (((FiniteComputes.ofPoly (ReverseFold.startComputes ea eb)).andThen
    (Iterate.computes (ReverseFold.encoding ea eb) (ReverseFold.step d f)
      (ReverseFold.stepComputes ea eb d f cell))).andThen
    (FiniteComputes.ofPoly (ReverseFold.acc ea eb)))
  have hrun : ((ReverseFold.computes ea eb d f cell).outputs q).steps=
      (run.outputs q).steps := by
    dsimp only [ReverseFold.computes,FiniteComputes.congr]
    exact output_cast_steps run.machine rfl
      (congrArg eb.encode (congrArg
        (fun s : ReverseFold.State (A := A) (B := B) => s.2.2)
        (ReverseFold.byte_iterations ea eb d f q))) rfl (run.outputs q) _
  rw [hrun]
  change ((ReverseFold.acc ea eb).outputs v).steps+
    (2*(((ReverseFold.encoding ea eb).encode v).length+1)+
      (((Iterate.computes (ReverseFold.encoding ea eb) (ReverseFold.step d f)
        (ReverseFold.stepComputes ea eb d f cell)).outputs s).steps+
          (2*(((ReverseFold.encoding ea eb).encode s).length+1)+
            ((ReverseFold.startComputes ea eb).outputs q).steps)))≤_
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

def after {C : Type} {ec : Encoding C Bool} {q : C → List A × B}
    {prepare : FiniteComputes ec (ReverseFold.inputEncoding ea eb) q}
    (p : Timing prepare) (t : Timing cell) (W : Polynomial ℕ)
    (hs : ∀ c k,((ReverseFold.encoding ea eb).encode
      (((ReverseFold.step d f)^[k]) (ReverseFold.start (q c)))).length≤W.eval (ec.encode c).length) :
    Timing (prepare.andThen (ReverseFold.computes ea eb d f cell)) :=
  p.after (time ea eb d f t p.width W) (fun c =>
    steps ea eb d f t p.width W (q c) (ec.encode c).length (p.output_length c) (hs c))
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.Fold
