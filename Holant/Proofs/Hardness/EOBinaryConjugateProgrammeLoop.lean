import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeWidth
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateCall
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterateFinish

/-! Actual finite loop for the collision-aware interpolation controller. Its
counter is a physical copy of the initial state bytes, including the unary
padding for all nested root scans. Every intermediate arithmetic width and
every completed transition count is bounded by explicit polynomials. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeLoop
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient StackProtocol
open FixedGadgetSubstitution.Compiler
namespace S
export EOBinaryConjugateProgrammeState (State step encoding computes finishComputes)
export EOBinaryConjugateProgrammeBounds (Bounded)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {K A : Type} [Field K] [Algebra ℚ K] [Fintype A] {n : ℕ}
variable (F : FixedField K n)

def inputEncoding : Encoding (S.State K) Bool where
  encode s := frame ((S.encoding F).encode s)
  decode bits := do
    let (word,rest) ← unframe bits
    if rest=[] then (S.encoding F).decode word else none
  decode_encode s := by
    have hf := unframe_frame_append ((S.encoding F).encode s) []
    simp only [List.append_nil] at hf
    change (unframe (frame ((S.encoding F).encode s))).bind _ = some s
    rw [hf]
    simp only [Option.bind_some,ite_true]
    exact (S.encoding F).decode_encode s

def provider : Computes (pairEncoding (S.encoding F) Frame.wordEncoding) (S.encoding F)
    (fun x => S.step x.1) :=
  (Wiring.firstComputes (S.encoding F) Frame.wordEncoding).andThen (S.computes F)

def machine := BitmapIterate.machine (provider F).machine

def value (s : S.State K) := (S.step^[(S.encoding F |>.encode s).length]) s

variable (base : A→Fin n→ℚ) (R U V L : Polynomial ℕ)

def budget : Polynomial ℕ := R+U+V+(L+1)*(R+3)+L*(U+R+(L+1)*(R+3)+4)
def fieldWidth : Polynomial ℕ :=
  (BinaryInterpolation.RingFormulaMachine.widthPolynomial F base).comp (budget R U V L)
def width : Polynomial ℕ := 100*(fieldWidth F base R U V L+1)*(L+1)

def roundPolynomial : Polynomial ℕ :=
  (provider F).time.comp (2*width F base R U V L+1)+7*width F base R U V L+11

def timePolynomial : Polynomial ℕ :=
  5*L+8+L*roundPolynomial F base R U V L+2*width F base R U V L+5

@[simp] theorem width_eval (N : ℕ) : (width F base R U V L).eval N=
    100*(Holant.OneHot.ArithmeticSize.bitBound F base
      (EOBinaryConjugateProgrammeWidth.budget (R.eval N) (U.eval N) (V.eval N) (L.eval N))+1)*(L.eval N+1) := by
  classical
  simp [width,fieldWidth,budget,EOBinaryConjugateProgrammeWidth.budget,
    BinaryInterpolation.RingFormulaMachine.width_eval]

variable (unit minus : A) (hunit : F.decode (base unit)=1) (hminus : F.decode (base minus) = -1)

include unit minus hunit hminus in
theorem iterate_width (N : ℕ) (s : S.State K)
    (h : S.Bounded (fun a=>F.decode (base a)) (R.eval N) (U.eval N) (V.eval N) s)
    (hs : (S.encoding F |>.encode s).length≤L.eval N) (i : ℕ) (hi : i≤L.eval N) :
    (S.encoding F |>.encode ((S.step^[i]) s)).length≤(width F base R U V L).eval N := by
  rw [width_eval]
  exact EOBinaryConjugateProgrammeWidth.iterate_encoding F base unit minus hunit hminus h hs i hi

include unit minus hunit hminus in
theorem loop_run (N : ℕ) (s : S.State K)
    (h : S.Bounded (fun a=>F.decode (base a)) (R.eval N) (U.eval N) (V.eval N) s)
    (hs : (S.encoding F |>.encode s).length≤L.eval N)
    (k i : ℕ) (hki : i+k≤L.eval N) :
    ∃time,time≤k*(roundPolynomial F base R U V L).eval N ∧
      RunsExactly (machine F).computer.step
        (BitmapIterate.ready (provider F).machine (BitmapIterate.phase (provider F).machine 5)
          ((S.encoding F).encode ((S.step^[i]) s)) [] (List.replicate k true) [] [] [])
        (BitmapIterate.ready (provider F).machine (BitmapIterate.phase (provider F).machine 5)
          ((S.encoding F).encode ((S.step^[i+k]) s)) [] [] [] [] []) time := by
  induction k generalizing i with
  | zero => exact ⟨0,by simp,by simp [RunsExactly]⟩
  | succ k ih =>
    let current := (S.step^[i]) s
    let next := S.step current
    let w := (provider F).outputs (current,([] : List Bool))
    have hc := iterate_width F base R U V L unit minus hunit hminus N s h hs i (by omega)
    have hn := iterate_width F base R U V L unit minus hunit hminus N s h hs (i+1) (by omega)
    have next_eq : next=(S.step^[i+1]) s := by
      simp only [next,current,Function.iterate_succ_apply']
    have hp : w.steps≤(provider F).time.eval (2*(width F base R U V L).eval N+1) := by
      apply w.steps_le_m.trans
      apply natPolynomial_eval_mono
      rw [pairEncoding_length]
      change 2*((S.encoding F).encode current).length+1+0≤_
      dsimp only [current]
      omega
    have first := BitmapIterate.round_exact (provider F).machine
      ((S.encoding F).encode current) (List.replicate k true) [] []
      ((S.encoding F).encode next) w.steps
      (by simpa [pairEncoding,Frame.wordEncoding,next,Function.flip_def] using w.evals_in_steps)
    obtain ⟨t,ht,rest⟩ := ih (i+1) (by omega)
    have hb : w.steps+5*((S.encoding F).encode current).length+
        2*((S.encoding F).encode next).length+11≤(roundPolynomial F base R U V L).eval N := by
      rw [next_eq]
      simp only [roundPolynomial,Polynomial.eval_add,Polynomial.eval_comp,
        Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,current]
      omega
    refine ⟨t+(w.steps+5*((S.encoding F).encode current).length+
      2*((S.encoding F).encode next).length+11),by nlinarith,?_⟩
    rw [←next_eq] at rest
    have hi : i+1+k=i+(k+1) := by omega
    simpa only [machine,List.length_nil,Nat.mul_zero,Nat.add_zero,List.replicate_succ,hi,current,
      BitmapIterate.machine,Machine.computer,FinTM2.step] using first.trans rest

include unit minus hunit hminus in
theorem whole_run (N : ℕ) (s : S.State K)
    (h : S.Bounded (fun a=>F.decode (base a)) (R.eval N) (U.eval N) (V.eval N) s)
    (hs : (S.encoding F |>.encode s).length≤L.eval N) :
    ∃time,time≤(timePolynomial F base R U V L).eval N ∧
      RunsExactly (machine F).computer.step
        (initList (machine F).computer ((inputEncoding F).encode s))
        (haltList (machine F).computer ((S.encoding F).encode (value F s))) time := by
  let count := ((S.encoding F).encode s).length
  have prep := BitmapIterate.prepare (provider F).machine ((S.encoding F).encode s) []
  obtain ⟨t,ht,loop⟩ := loop_run F base R U V L unit minus hunit hminus N s h hs count 0 (by simpa [count] using hs)
  have last := BitmapIterate.finish (provider F).machine
    ((S.encoding F).encode ((S.step^[count]) s)) [] []
  have hout := iterate_width F base R U V L unit minus hunit hminus N s h hs count hs
  have all := (prep.trans (by
    simpa [count,machine,BitmapIterate.machine,Machine.computer,FinTM2.step] using loop)).trans last
  refine ⟨(2*((S.encoding F).encode ((S.step^[count]) s)).length+5)+(t+(5*count+8)),?_,?_⟩
  · have hm := Nat.mul_le_mul_right ((roundPolynomial F base R U V L).eval N) hs
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    dsimp only [count] at ht hout ⊢
    omega
  · unfold machine
    rw [BitmapIterate.initial]
    simpa only [machine,inputEncoding,value,List.length_nil,Nat.mul_zero,Nat.add_zero,
      Nat.zero_add,List.append_nil,count,FinTM2.step] using all

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeLoop
