import Holant.Proofs.CountingMachines.StandardMachine.InputRecoding
import Holant.Proofs.CountingMachines.StandardMachine.Recoding.Composition
import Holant.Proofs.CountingMachines.StandardMachine.ReversePhysical
import Holant.Proofs.CountingMachines.StandardMachine.TapeAdapter.Paths

set_option backward.isDefEq.respectTransparency false
/-! Genuine finite recoding of a witness verifier, including its tagged input
and its clean Boolean output. No composed verifier, compiled-machine correctness
or runtime bound is supplied. The original witness vectors are unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.ReencodedWitness
open Turing Computability Holant.Complexity
variable {α Γ Δ : Type} [Fintype Γ] [Fintype Δ]
variable (ea : Encoding α Γ) (eb : Encoding α Δ) (code : Γ → List Δ)
variable (encoded : ∀ a, eb.encode a = (ea.encode a).flatMap code)
variable {f : α → ℕ} (w : SharpPWitness eb f)

/-- Actual tagged input recoder, old verifier, then actual output retagger. -/
def verifier : PolyTime (encodingProd ea (encodingList Bool)) (taggedBoolEncoding Γ) w.accept := by
  let first : PolyTime (encodingProd ea (encodingList Bool)) (taggedBoolEncoding Δ) (w.accept ∘ id) :=
    Recoding.Composition.comp (f := id) (g := w.accept) (InputRecoding.tagged ea eb code encoded)
      w.verifier (InputRecoding.taggedBound ea eb code encoded)
  let size : PolynomialOutputBound (encodingProd ea (encodingList Bool))
      (taggedBoolEncoding Δ) (w.accept ∘ id) := ⟨1,fun _ => by simp⟩
  exact Recoding.Composition.comp (f := w.accept ∘ id) (g := id) first (InputRecoding.retag (Γ := Γ) (Δ := Δ)) size

variable (width : ℕ) (fixed : ∀ letter, (code letter).length = width)

include fixed in
theorem fixed_word_length (word : List Γ) :
    (word.flatMap code).length = width * word.length := by
  induction word with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.flatMap_cons,List.length_append,fixed,ih,List.length_cons,Nat.mul_succ]
      omega

include encoded fixed in
theorem encoded_length (a : α) : (eb.encode a).length = width * (ea.encode a).length := by
  rw [encoded]
  exact fixed_word_length code width fixed _

/-- Exact original-input witness constructor. The source bound is transported
by the proved fixed width; its verifier is the actual three-stage program. -/
def source : SharpPWitness ea f where
  witnessLength := w.witnessLength.comp (Polynomial.C width * Polynomial.X)
  accept := w.accept
  verifier := verifier ea eb code encoded w
  counts a := by
    simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      encoded_length ea eb code encoded width fixed a] using w.counts a

private def acceptedCast {n k : ℕ} (h : n = k) (A : List Bool → Bool) :
    {x : Fin n → Bool // A (List.ofFn x) = true} ≃
      {x : Fin k → Bool // A (List.ofFn x) = true} where
  toFun x := ⟨fun i => x.val (Fin.cast h.symm i),by
    rw [← List.ofFn_congr h x.val]
    exact x.property⟩
  invFun x := ⟨fun i => x.val (Fin.cast h i),by
    rw [← List.ofFn_congr h.symm x.val]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (by apply Fin.ext; rfl)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (by apply Fin.ext; rfl)

def acceptedEquiv (a : α) :
    {bits : Fin ((source ea eb code encoded w width fixed).witnessLength.eval (ea.encode a).length) → Bool //
      (source ea eb code encoded w width fixed).accept (a,List.ofFn bits) = true} ≃
    {bits : Fin (w.witnessLength.eval (eb.encode a).length) → Bool //
      w.accept (a,List.ofFn bits) = true} :=
  acceptedCast (by
    change (w.witnessLength.comp (Polynomial.C width * Polynomial.X)).eval (ea.encode a).length = _
    simp only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      encoded_length ea eb code encoded width fixed a]) (fun bits => w.accept (a,bits))

/-- Recoding preserves the witness word literally; no fresh free or padding bits. -/
theorem accepted_word (a : α)
    (p : {bits : Fin ((source ea eb code encoded w width fixed).witnessLength.eval (ea.encode a).length) → Bool //
      (source ea eb code encoded w width fixed).accept (a,List.ofFn bits) = true}) :
    List.ofFn (acceptedEquiv ea eb code encoded w width fixed a p).val = List.ofFn p.val := by
  have hlen : (source ea eb code encoded w width fixed).witnessLength.eval (ea.encode a).length =
      w.witnessLength.eval (eb.encode a).length := by
    simp only [source,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      encoded_length ea eb code encoded width fixed a]
  exact (List.ofFn_congr hlen p.val).symm

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.ReencodedWitness

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Model
open Turing Computability Holant.Complexity
variable {α Γ Δ Q : Type} [Fintype Γ] [Fintype Δ] [Fintype Q]
variable (m : Model Δ Q) (ea : Encoding α Γ) (input : Γ → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

private def injectedWitness :
    SharpPWitness (InputRecoding.injectedEncoding ea input hinj)
      (m.physicalCount (InputRecoding.injectedEncoding ea input hinj)) :=
  m.physicalToWitness (InputRecoding.injectedEncoding ea input hinj) clock (fun a tokens finish ht => by
    simpa only [InputRecoding.injected_length] using htime (ea.encode a) tokens finish ht)

/-- The original external input alphabet and exact `ea` bytes are restored by
an actual one-symbol injection program and a clean result retagger. Time is
required only for declared input words, never all work-alphabet words. -/
def typedPhysicalToWitness :
    SharpPWitness ea (m.physicalCount (InputRecoding.injectedEncoding ea input hinj)) :=
  ReencodedWitness.source ea (InputRecoding.injectedEncoding ea input hinj)
    (fun letter => [input letter]) (fun a => by simp [InputRecoding.injectedEncoding])
    (injectedWitness m ea input hinj clock htime) 1 (fun _ => rfl)

include htime in
theorem typed_physical_inSharpP :
    InSharpP ea (m.physicalCount (InputRecoding.injectedEncoding ea input hinj)) :=
  ⟨m.typedPhysicalToWitness ea input hinj clock htime⟩

/-- Both directions are explicit maps between actual accepted witness vectors
of the generated verifier and actual independently defined physical paths. -/
def typedPhysicalWitnessEquiv (a : α) :
    m.PhysicalPath ((ea.encode a).map input) ≃
      {bits : Fin ((m.typedPhysicalToWitness ea input hinj clock htime).witnessLength.eval
          (ea.encode a).length) → Bool //
        (m.typedPhysicalToWitness ea input hinj clock htime).accept (a,List.ofFn bits) = true} :=
  (m.verifierWitnessEquiv (InputRecoding.injectedEncoding ea input hinj) clock
    (fun a tokens finish ht => by
      simpa only [InputRecoding.injected_length] using htime (ea.encode a) tokens finish ht) a).trans
    (ReencodedWitness.acceptedEquiv ea (InputRecoding.injectedEncoding ea input hinj)
      (fun letter => [input letter]) (fun a => by simp [InputRecoding.injectedEncoding])
      (injectedWitness m ea input hinj clock htime) 1 (fun _ => rfl) a).symm

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Model
