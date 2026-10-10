import Holant.Proofs.CountingMachines.StandardMachine.TapeAdapter.Codec
import Holant.Proofs.CountingMachines.StandardMachine.Support.NDPrimitiveAcceptControl.Source

set_option backward.isDefEq.respectTransparency false
/-! Concrete arbitrary-alphabet witness compilation into the independent
finite zipper machine. Source polynomial bounds are used only on raw Boolean
input words; no bound on arbitrary work-alphabet input is asserted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.TapeAdapter.Instantiation
open Turing Computability Holant.Complexity
open Support
namespace P
export NDPrimitiveAcceptControl.Program (Symbol Control Phase table choose initial)
end P
namespace AP
export NDPrimitiveAcceptControl.Paths (Trace Path originalPathsEquiv count encoded_count)
end AP
namespace AS
export NDPrimitiveAcceptControl.Source (clock time)
end AS
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ} (w : SharpPWitness ea f)

def verdict : P.Control w → Option Bool
  | .inr .accept => some true
  | .inr .reject => some false
  | _ => none

def primitive : Primitive (P.Symbol w) (P.Control w) where
  table := P.table w
  split := P.choose w
  main := default
  verdict := verdict w
  halted := by
    intro q h bit a
    cases q with
    | inl q => simp [verdict] at h
    | inr phase => cases phase <;> simp_all [verdict,P.table]

def input : Bool → P.Symbol w := NDPrimitiveFrontend.Program.Symbol.raw

theorem input_injective : Function.Injective (input w) := by
  intro a b h
  exact NDPrimitiveFrontend.Program.Symbol.raw.inj h

theorem input_ne_blank (bit : Bool) : input w bit ≠ default := by
  intro h
  cases h

@[simp] theorem step_eq (token : Option Bool) (c : TM0.Cfg (P.Symbol w) (P.Control w)) :
    (primitive w).step token c = NDPrimitiveAcceptControl.Program.step w token c := rfl

@[simp] theorem initial_eq (word : List Bool) :
    (primitive w).initial (word.map (input w)) = P.initial w word := rfl

theorem trace_iff (tokens : List (Option Bool))
    (a b : TM0.Cfg (P.Symbol w) (P.Control w)) :
    (primitive w).Trace tokens a b ↔ AP.Trace w tokens a b := by
  induction tokens generalizing a with
  | nil => rfl
  | cons token rest ih => simp only [Primitive.Trace,AP.Trace,step_eq,ih]

@[simp] theorem verdict_accept (q : P.Control w) : verdict w q = some true ↔ q = .inr .accept := by
  cases q with
  | inl q => simp [verdict]
  | inr phase => cases phase <;> simp [verdict]

def sourcePathEquiv (word : List Bool) :
    AP.Path w word ≃ (primitive w).Path (word.map (input w)) where
  toFun := fun path => ⟨path.val, by
    obtain ⟨T,hT⟩ := path.property
    refine ⟨⟨.inr .accept,T⟩,rfl,?_⟩
    exact (trace_iff w path.val _ _).mpr hT⟩
  invFun := fun path => ⟨path.val, by
    obtain ⟨finish,ha,ht⟩ := path.property
    have hq : finish.q = .inr .accept := (verdict_accept w finish.q).mp ha
    refine ⟨finish.Tape,?_⟩
    have he : finish = ⟨.inr .accept,finish.Tape⟩ := by cases finish; simp_all
    rw [he] at ht
    exact (trace_iff w path.val _ _).mp ht⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

def machine : Model (P.Symbol w) (Option (P.Control w)) := (primitive w).model

def clock : Polynomial ℕ := AS.clock w + Polynomial.C 1

theorem primitive_time : (primitive w).PolyTimeOn (input w) (AS.clock w) := by
  intro word tokens finish ht
  apply AS.time w word tokens finish
  exact (trace_iff w tokens _ _).mp ht

theorem time : (machine w).PolyTimeOn (input w) (clock w) :=
  (primitive w).model_polyTimeOn (input w) (AS.clock w) (primitive_time w)

def physicalPathEquiv (word : List Bool) :
    AP.Path w word ≃ (machine w).PhysicalPath (word.map (input w)) :=
  (sourcePathEquiv w word).trans ((primitive w).pathEquiv _)

@[simp] theorem physicalPathEquiv_labels (word : List Bool) (path : AP.Path w word) :
    (physicalPathEquiv w word path).val = path.val := rfl

def paddedPathEquiv (word : List Bool) :
    AP.Path w word ≃
      (machine w).AcceptedPath ((clock w).eval word.length) (word.map (input w)) :=
  (sourcePathEquiv w word).trans
    ((primitive w).paddedPathEquiv (input w) (AS.clock w) (primitive_time w) word)

/-- The original arbitrary finite input/stack alphabet is retained by the
source witness; only this machine's external input channel is Boolean. -/
def witnessPhysicalEquiv (a : α) :
    ConventionalSharpPSource.AcceptedWitness w a ≃
      (machine w).PhysicalPath ((TotalRawSource.encodedInput w a).map (input w)) :=
  (AP.originalPathsEquiv w a).trans (physicalPathEquiv w _)

def witnessPaddedEquiv (a : α) :
    ConventionalSharpPSource.AcceptedWitness w a ≃
      (machine w).AcceptedPath ((clock w).eval (TotalRawSource.encodedInput w a).length)
        ((TotalRawSource.encodedInput w a).map (input w)) :=
  (AP.originalPathsEquiv w a).trans (paddedPathEquiv w _)

theorem physical_count (a : α) :
    Nat.card ((machine w).PhysicalPath ((TotalRawSource.encodedInput w a).map (input w))) = f a := by
  rw [← Nat.card_congr (physicalPathEquiv w (TotalRawSource.encodedInput w a))]
  simpa only [Nat.card_eq_fintype_card,AP.count] using AP.encoded_count w a

theorem padded_count (a : α) :
    Nat.card ((machine w).AcceptedPath ((clock w).eval (TotalRawSource.encodedInput w a).length)
      ((TotalRawSource.encodedInput w a).map (input w))) = f a := by
  rw [← Nat.card_congr (paddedPathEquiv w (TotalRawSource.encodedInput w a))]
  simpa only [Nat.card_eq_fintype_card,AP.count] using AP.encoded_count w a


/-- Read only literal raw input letters. In particular, false is not blank. -/
def readInput : List (P.Symbol w) → Option (List Bool)
  | [] => some []
  | .raw bit :: rest => (readInput rest).map (bit :: ·)
  | _ :: _ => none

@[simp] theorem readInput_map (word : List Bool) :
    readInput w (word.map (input w)) = some word := by
  induction word with
  | nil => rfl
  | cons bit rest ih => simpa [input,readInput] using congrArg (Option.map (bit :: ·)) ih

/-- This decoder is metadata certifying faithful input representation. It is
not called as an oracle or instruction by the machine. -/
def inputEncoding : Encoding α (P.Symbol w) where
  encode a := (TotalRawSource.encodedInput w a).map (input w)
  decode word := (readInput w word).bind (TotalRawSource.inputEncoding w).decode
  decode_encode a := by
    rw [readInput_map,Option.bind_some]
    exact Encoding.decode_encode (TotalRawSource.inputEncoding w) a

/-- Faithfulness also holds for the actual initialized tape configuration,
not only for its metadata word encoding. -/
theorem initialEncoding_injective : Function.Injective
    (fun a => (machine w).initialConfig ((inputEncoding w).encode a)) := by
  intro a b h
  have he := (machine w).initialConfig_map_injective (input w) (input_injective w)
    (input_ne_blank w) h
  exact Encoding.encode_injective (TotalRawSource.inputEncoding w) he

theorem encoded_length (a : α) :
    ((inputEncoding w).encode a).length = TotalRawSource.encodedWidth w * (ea.encode a).length := by
  simp only [inputEncoding,List.length_map,TotalRawSource.encoded_length]

/-- The concrete machine's time measured in original input symbols, not its
longer Boolean protocol or its still larger internal work alphabet. -/
def originalClock : Polynomial ℕ :=
  (clock w).comp (Polynomial.C (TotalRawSource.encodedWidth w) * Polynomial.X)

theorem clock_eval_original (a : α) :
    (clock w).eval (TotalRawSource.encodedInput w a).length =
      (originalClock w).eval (ea.encode a).length := by
  simp only [originalClock,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,TotalRawSource.encoded_length]

theorem encoded_time (a : α) (tokens : List (Option Bool))
    (finish : Config (P.Symbol w) (Option (P.Control w)))
    (ht : (machine w).PhysicalTrace tokens ((machine w).initialConfig ((inputEncoding w).encode a)) finish) :
    tokens.length ≤ (originalClock w).eval (ea.encode a).length := by
  rw [← clock_eval_original]
  exact time w (TotalRawSource.encodedInput w a) tokens finish ht

/-- Every typed encoded-input prefix extends to an actual stopped control
inside the same original-size clock, including rejecting executions. -/
theorem encoded_completion (a : α) (tokens : List (Option Bool))
    (finish : Config (P.Symbol w) (Option (P.Control w)))
    (ht : (machine w).PhysicalTrace tokens ((machine w).initialConfig ((inputEncoding w).encode a)) finish) :
    ∃ rest endCfg, (machine w).PhysicalTrace rest finish endCfg ∧
      ((machine w).verdict endCfg.control).isSome = true ∧
      (tokens ++ rest).length ≤ (originalClock w).eval (ea.encode a).length := by
  rw [← clock_eval_original]
  exact (machine w).polyTimeOn_completion (input w) (clock w) (time w)
    (TotalRawSource.encodedInput w a) tokens finish ht

def originalSpacePolynomial : Polynomial ℕ :=
  Polynomial.C (TotalRawSource.encodedWidth w) * Polynomial.X + originalClock w + Polynomial.C 1

theorem encoded_cells (a : α) (tokens : List (Option Bool))
    (finish : Config (P.Symbol w) (Option (P.Control w)))
    (ht : (machine w).PhysicalTrace tokens ((machine w).initialConfig ((inputEncoding w).encode a)) finish) :
    (machine w).cells finish ≤ (originalSpacePolynomial w).eval (ea.encode a).length := by
  have hs := (machine w).prefix_cells ((inputEncoding w).encode a) tokens finish
    ((machine w).physicalTrace_trace tokens _ finish ht)
  have hb := encoded_time w a tokens finish ht
  rw [encoded_length] at hs
  simp only [originalSpacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  omega

/-- Literal Boolean encoding size, transported to the original input length. -/
def originalBitsPolynomial : Polynomial ℕ :=
  (Codec.storagePolynomial (Γ := P.Symbol w) (Q := Option (P.Control w)) (clock w)).comp
    (Polynomial.C (TotalRawSource.encodedWidth w) * Polynomial.X)

theorem encoded_bits (a : α) (tokens : List (Option Bool))
    (finish : Config (P.Symbol w) (Option (P.Control w)))
    (ht : (machine w).PhysicalTrace tokens ((machine w).initialConfig ((inputEncoding w).encode a)) finish) :
    (Codec.configEncoding.encode finish).length ≤
      (originalBitsPolynomial w).eval (ea.encode a).length := by
  have hb := Codec.prefix_bits (machine w) (input w) (clock w) (time w)
    (TotalRawSource.encodedInput w a) tokens finish ht
  simpa only [originalBitsPolynomial,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,TotalRawSource.encoded_length] using hb

/-- Closed forward output: generated physical machine, arbitrary-alphabet
witness bijection and count, and original-size physical resource bounds. -/
theorem witness_forward (a : α) :
    Nonempty (ConventionalSharpPSource.AcceptedWitness w a ≃
      (machine w).PhysicalPath ((inputEncoding w).encode a)) ∧
    Nat.card ((machine w).PhysicalPath ((inputEncoding w).encode a)) = f a ∧
    ∀ (tokens : List (Option Bool)) (finish : Config (P.Symbol w) (Option (P.Control w))),
      (machine w).PhysicalTrace tokens ((machine w).initialConfig ((inputEncoding w).encode a)) finish →
      tokens.length ≤ (originalClock w).eval (ea.encode a).length ∧
      (machine w).cells finish ≤ (originalSpacePolynomial w).eval (ea.encode a).length ∧
      (Codec.configEncoding.encode finish).length ≤ (originalBitsPolynomial w).eval (ea.encode a).length :=
  ⟨⟨witnessPhysicalEquiv w a⟩,physical_count w a,
    fun tokens finish ht => ⟨encoded_time w a tokens finish ht,encoded_cells w a tokens finish ht,
      encoded_bits w a tokens finish ht⟩⟩

/-- The full forward receipt retains physical-input faithfulness as well as
the accepted-witness bijection and actual original-size resource bounds. -/
theorem faithful_forward :
    Function.Injective (fun a => (machine w).initialConfig ((inputEncoding w).encode a)) ∧
    ∀ a : α,
      Nonempty (ConventionalSharpPSource.AcceptedWitness w a ≃
        (machine w).PhysicalPath ((inputEncoding w).encode a)) ∧
      Nat.card ((machine w).PhysicalPath ((inputEncoding w).encode a)) = f a ∧
      ∀ (tokens : List (Option Bool)) (finish : Config (P.Symbol w) (Option (P.Control w))),
        (machine w).PhysicalTrace tokens ((machine w).initialConfig ((inputEncoding w).encode a)) finish →
        tokens.length ≤ (originalClock w).eval (ea.encode a).length ∧
        (machine w).cells finish ≤ (originalSpacePolynomial w).eval (ea.encode a).length ∧
        (Codec.configEncoding.encode finish).length ≤ (originalBitsPolynomial w).eval (ea.encode a).length :=
  ⟨initialEncoding_injective w,witness_forward w⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.TapeAdapter.Instantiation
