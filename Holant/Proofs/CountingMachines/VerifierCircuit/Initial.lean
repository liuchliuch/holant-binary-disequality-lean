import Holant.Proofs.CountingMachines.VerifierCircuit.Unroll

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Initialization from literal input bytes and free witness wires

Ported reference proof. See the task validation reports.

Input tokens name a constant original bit or one existing witness register.
They are not extra variables. The tagged concatenation is exactly the library
`encodingProd`; no additional delimiter or guessed configuration is used.
-/

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Initial


open Turing Computability BitLayout
open scoped Classical

def tokens (word : List Bool) (W : ℕ) : List (Bool ⊕ Fin W) :=
  word.map Sum.inl ++ (List.finRange W).map Sum.inr

def tokenValue {W : ℕ} (bits : Fin W → Bool) : Bool ⊕ Fin W → Bool ⊕ Bool :=
  Sum.elim Sum.inl (fun i => Sum.inr (bits i))

theorem tokens_map (word : List Bool) (W : ℕ) (bits : Fin W → Bool) :
    (tokens word W).map (tokenValue bits) = word.map Sum.inl ++ (List.ofFn bits).map Sum.inr := by
  simp [tokens, tokenValue, List.map_map, List.ofFn_eq_map, Function.comp_def]

variable (tm : FinTM2) (C : ℕ) [∀ k, Fintype (tm.Γ k)]
variable (e : tm.Γ tm.k₀ ≃ Bool ⊕ Bool) (word : List Bool) (W : ℕ)

def inputWord (bits : Fin W → Bool) : List (tm.Γ tm.k₀) :=
  ((tokens word W).map (tokenValue bits)).map e.symm

@[simp] theorem inputWord_length (bits : Fin W → Bool) :
    (inputWord tm e word W bits).length = word.length + W := by
  simp [inputWord, tokens]

/-- A fixed six-gate implementation is used even for constant unary functions;
the free wire is routed, never assigned by an internal witness. -/
def boolMap {I : Type} (i : I) (f : Bool → Bool) : Emit I Unit :=
  Emit.seq (Emit.parallel (Emit.route (fun _ : Unit => i))
    (Emit.parallel (Emit.constant (f true)) (Emit.constant (f false))))
    (Emit.mux (.inl ()) (.inr (.inl ())) (.inr (.inr ())))

theorem boolMap_denotes {I : Type} (i : I) (f : Bool → Bool) :
    Emit.Denotes (boolMap i f) (fun x _ => f (x i)) := by
  have h := Emit.seq_denotes (Emit.parallel_denotes (Emit.route_denotes (fun _ : Unit => i))
    (Emit.parallel_denotes (Emit.constant_denotes (f true)) (Emit.constant_denotes (f false))))
      (Emit.mux_denotes (.inl ()) (.inr (.inl ())) (.inr (.inr ())))
  have hb (x : I → Bool) : (if x i then f true else f false) = f (x i) := by
    cases x i <;> rfl
  change Emit.Denotes (boolMap i f) (fun x _ => if x i then f true else f false) at h
  have he : (fun (x : I → Bool) (_ : Unit) => if x i then f true else f false) =
      (fun x _ => f (x i)) := funext (fun x => funext (fun _ => hb x))
  rw [he] at h
  exact h

theorem boolMap_adds {I : Type} (i : I) (f : Bool → Bool) : Emit.Adds (boolMap i f) 6 :=
  Emit.seq_adds (Emit.parallel_adds (Emit.route_adds _)
    (Emit.parallel_adds (Emit.constant_adds _) (Emit.constant_adds _))) (Emit.mux_adds _ _ _)

def inputBit (i : Fin (C + 1)) (a : Option (tm.Γ tm.k₀)) : Emit (Fin W) Unit :=
  match (tokens word W)[i.val]? with
  | none => Emit.constant (oneHot (none : Option (tm.Γ tm.k₀)) a)
  | some (.inl b) => Emit.constant (oneHot (some (e.symm (.inl b))) a)
  | some (.inr j) => boolMap j (fun b => oneHot (some (e.symm (.inr b))) a)

theorem inputBit_denotes (i : Fin (C + 1)) (a : Option (tm.Γ tm.k₀)) :
    Emit.Denotes (inputBit tm C e word W i a)
      (fun bits _ => oneHot ((inputWord tm e word W bits)[i.val]?) a) := by
  unfold inputBit
  cases h : (tokens word W)[i.val]? with
  | none => simpa [inputWord, h] using
      (Emit.constant_denotes (I := Fin W) (oneHot (none : Option (tm.Γ tm.k₀)) a))
  | some token =>
    cases token with
    | inl b => simpa [inputWord, h, tokenValue] using
        (Emit.constant_denotes (I := Fin W) (oneHot (some (e.symm (.inl b))) a))
    | inr j => simpa [inputWord, h, tokenValue] using
        boolMap_denotes j (fun b => oneHot (some (e.symm (.inr b))) a)

def bit : Address tm C → Emit (Fin W) Unit
  | .inl l => Emit.constant (oneHot (some tm.main) l)
  | .inr (.inl s) => Emit.constant (oneHot tm.initialState s)
  | .inr (.inr ⟨k, i, a⟩) =>
    if h : k = tm.k₀ then inputBit tm C e word W i (h ▸ a)
    else Emit.constant (oneHot (none : Option (tm.Γ k)) a)

theorem bit_denotes (a : Address tm C) :
    Emit.Denotes (bit tm C e word W a)
      (fun bits _ => encode tm C (PackedStep.packRaw tm C (initList tm (inputWord tm e word W bits))) a) := by
  cases a with
  | inl l => exact Emit.constant_denotes _
  | inr a =>
    cases a with
    | inl s => exact Emit.constant_denotes _
    | inr a =>
      rcases a with ⟨k, i, a⟩
      by_cases hk : k = tm.k₀
      · subst k
        simpa [bit, encode, PackedStep.packRaw, initList, BoundedTableau.pad] using
          inputBit_denotes tm C e word W i a
      · simpa [bit, hk, encode, PackedStep.packRaw, initList, BoundedTableau.pad] using
          (Emit.constant_denotes (I := Fin W) (oneHot (none : Option (tm.Γ k)) a))

def emit : Emit (Fin W) (Address tm C) :=
  Emit.tabulate (addresses tm C) (mem_addresses tm C) (bit tm C e word W)

theorem denotes : Emit.Denotes (emit tm C e word W)
    (fun bits => encode tm C (PackedStep.packRaw tm C (initList tm (inputWord tm e word W bits)))) :=
  Emit.tabulate_denotes _ _ _ _ (bit_denotes tm C e word W)

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Initial
