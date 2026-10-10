import Holant.Proofs.CountingMachines.AnswerDecoder.Native
import Holant.Complexity.FramedEncoding
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Faithful physical configuration serialization. A fixed finite numbering is
used only for control and stack addresses; every stored bit is retained. This
observer does not claim constant-time serialization or add a machine opcode. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Storage
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose
open scoped BigOperators

/-- Concrete parseable framing of the control labels, state and all tape words. -/
def dataEncoding : Encoding (ℕ × (ℕ × List (List Bool))) Bool :=
  framedProductEncoding encodingNatBool
    (framedProductEncoding encodingNatBool (framedListEncoding (encodingList Bool)))

def configurationData (m : Machine) (c : m.Config) : ℕ × (ℕ × List (List Bool)) :=
  ((Fintype.equivFin (Option m.Label) c.l).val,
   (Fintype.equivFin m.State c.var).val,
   List.ofFn (fun i => c.stk ((Fintype.equivFin m.K).symm i)))

def configurationWord (m : Machine) (c : m.Config) : List Bool :=
  dataEncoding.encode (configurationData m c)

/-- The concrete framed parser recovers every physical component exactly. -/
@[simp] theorem configurationWord_parses (m : Machine) (c : m.Config) :
    dataEncoding.decode (configurationWord m c) = some (configurationData m c) :=
  dataEncoding.decode_encode _

/-- No two complete configurations share a code, including halted control. -/
theorem configurationData_injective (m : Machine) : Function.Injective (configurationData m) := by
  intro c d h
  have hl : c.l = d.l := (Fintype.equivFin (Option m.Label)).injective
    (Fin.ext (congrArg Prod.fst h))
  have hv : c.var = d.var := (Fintype.equivFin m.State).injective
    (Fin.ext (congrArg (fun x => x.2.1) h))
  have ht : c.stk = d.stk := by
    have hw := List.ofFn_injective (congrArg (fun x => x.2.2) h)
    funext k
    have hi := congrFun hw (Fintype.equivFin m.K k)
    simpa only [Equiv.symm_apply_apply] using hi
  cases c
  cases d
  cases hl
  cases hv
  cases ht
  rfl

theorem configurationWord_injective (m : Machine) : Function.Injective (configurationWord m) :=
  dataEncoding.encode_injective.comp (configurationData_injective m)

/-- The actual framing has exactly two bits of overhead per stack, plus its
terminator. Empty stacks remain visible in the serialized configuration. -/
theorem framedWords_length (xs : List (List Bool)) :
    ((framedListEncoding (encodingList Bool)).encode xs).length =
      2 * (xs.map List.length).sum + 2 * xs.length + 1 := by
  change (framedListEncode (encodingList Bool) xs).length = _
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [framedListEncode, List.length_cons, List.length_append, frame_length,
      encodingList, id_eq, List.map_cons, List.sum_cons] at *
    omega

def controlOverhead (m : Machine) : ℕ :=
  2 * (Fintype.card (Option m.Label)).size + 2 * (Fintype.card m.State).size +
    2 * Fintype.card m.K + 3

/-- Coded storage includes finite control, every tape's boundary and every bit. -/
theorem configurationWord_length (m : Machine) (c : m.Config) :
    (configurationWord m c).length ≤ 2 * stackSize c.stk + controlOverhead m := by
  have hl := Nat.size_le_size (Nat.le_of_lt (Fintype.equivFin (Option m.Label) c.l).isLt)
  have hv := Nat.size_le_size (Nat.le_of_lt (Fintype.equivFin m.State c.var).isLt)
  have hsum : ((List.ofFn (fun i => c.stk ((Fintype.equivFin m.K).symm i))).map
      List.length).sum = stackSize c.stk := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact (Fintype.equivFin m.K).symm.sum_comp (fun k => (c.stk k).length)
  simp only [configurationWord, dataEncoding, framedProductEncoding_length,
    configurationData, framedWords_length, List.length_ofFn, hsum,
    encodingNatBool, encodeNat_length, controlOverhead]
  omega

/-- Polynomial cost for the literal coded configuration of the decoder. -/
def codedPolynomial {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : FixedField K n) : Polynomial ℕ :=
  2 * scratchPolynomial F + Polynomial.C (controlOverhead (computes F).machine)

theorem decoder_coded_storage {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : FixedField K n) (y : K) (t : ℕ)
    (ht : t ≤ ((computes F).outputs y).steps) (d : (computes F).machine.Config)
    (hrun : (fun q => q.bind (computes F).machine.computer.step)^[t]
      (some (initList (computes F).machine.computer (F.encoding.encode y))) = some d) :
    (configurationWord (computes F).machine d).length ≤
      (codedPolynomial F).eval (F.encoding.encode y).length := by
  have hs := scratch_bound F y t ht d hrun
  have hc := configurationWord_length (computes F).machine d
  simp only [codedPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_C]
  omega

def nativeCodedPolynomial : Polynomial ℕ :=
  (codedPolynomial presentation).comp nativeAnswerBound.bound

theorem native_coded_storage (r : NativeInput) (t : ℕ)
    (ht : t ≤ (nativeComputes.outputs (nativeValue r)).steps)
    (d : nativeComputes.machine.Config)
    (hrun : (fun q => q.bind nativeComputes.machine.computer.step)^[t]
      (some (initList nativeComputes.machine.computer
        (presentation.encoding.encode (nativeValue r)))) = some d) :
    (configurationWord nativeComputes.machine d).length ≤
      nativeCodedPolynomial.eval (nativeInputEncoding.encode r).length := by
  exact (decoder_coded_storage presentation (nativeValue r) t ht d hrun).trans (by
    simpa only [nativeCodedPolynomial, Polynomial.eval_comp] using
      natPolynomial_eval_mono (codedPolynomial presentation) (native_answer_length r))

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Storage
