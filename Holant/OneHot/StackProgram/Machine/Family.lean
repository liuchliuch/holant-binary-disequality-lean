import Holant.OneHot.StackProgram.Machine.Kernels

/-! Disjoint finite worker families. The dependent sums and products are finite
control spaces fixed when the interpreter is built; input data remain on tapes. -/
namespace Holant.OneHot.StackProgram.Machine.Family
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
variable {I : Type} [Fintype I] [DecidableEq I] (workers : I → BinaryCompose.Machine)

abbrev Keys := Fin 4 ⊕ (i : I) × (workers i).K
abbrev Memory := (i : I) → (workers i).State
abbrev States := Option Bool × Memory workers
abbrev Labels := Fin 7 ⊕ (i : I) × (Fin 5 ⊕ (workers i).Label)
abbrev Config := StackProtocol.Cfg (Keys workers) (Labels workers) (Memory workers)
abbrev Statement := StackProtocol.Stmt (Keys workers) (Labels workers) (Memory workers)

def initial : Memory workers := fun i => (workers i).initial

def workerKey (i : I) (k : (workers i).K) : Keys workers := .inr ⟨i, k⟩
def workerLabel (i : I) (l : (workers i).Label) : Labels workers := .inr ⟨i, .inr l⟩
def control (i : I) (j : Fin 5) : Labels workers := .inr ⟨i, .inl j⟩

/-- Retained control tapes occur only in this mathematical representation. -/
def layout (i : I) (frame : Fin 4 → List Bool) : StackEmbedding (workers i).K (Keys workers) where
  key := workerKey workers i
  lift tapes
    | .inl k => frame k
    | .inr ⟨j, k⟩ => if h : j = i then tapes (h ▸ k) else []
  lookup tapes k := by simp [workerKey]
  update tapes k word := by
    funext key
    cases key with
    | inl k => simp [workerKey, Function.update]
    | inr pair =>
      rcases pair with ⟨j, key⟩
      by_cases hj : j = i
      · subst j
        by_cases hk : key = k
        · subst key; simp [workerKey, Function.update]
        · simp [workerKey, Function.update, hk]
      · simp [workerKey, Function.update, hj]

def states (i : I) : StateEmbedding (workers i).State (States workers) where
  put v := (none, Function.update (initial workers) i v)
  get v := v.2 i
  get_put v := by simp

omit [Fintype I] in
@[simp] theorem states_initial (i : I) :
    (states workers i).put (workers i).initial = (none, initial workers) := by
  simp [states, initial]

omit [Fintype I] in
/-- Embedding syntax depends only on the fixed key injection, never on frame data. -/
theorem embed_frame (i : I) (frame other : Fin 4 → List Bool)
    (q : TM2.Stmt (fun _ : (workers i).K => Bool) (workers i).Label (workers i).State) :
    embedStmt (layout workers i frame) (states workers i) (workerLabel workers i)
      (some (control workers i 2)) q =
    embedStmt (layout workers i other) (states workers i) (workerLabel workers i)
      (some (control workers i 2)) q := by
  induction q <;> simp only [embedStmt, *] <;> rfl

def tapes (code data opcode scratch : List Bool) : Keys workers → List Bool
  | .inl k => ![code, data, opcode, scratch] k
  | .inr _ => []

omit [Fintype I] in
@[simp] theorem layout_empty (i : I) (frame : Fin 4 → List Bool) :
    (layout workers i frame).lift (fun _ => []) = Sum.elim frame (fun _ => []) := by
  funext key
  cases key with
  | inl k => rfl
  | inr pair => rcases pair with ⟨j, k⟩; simp [layout]

/-- A worker's clean word is embedded at exactly one physical tape. -/
theorem layout_word (i : I) (frame : Fin 4 → List Bool) (k : (workers i).K) (word : List Bool) :
    (layout workers i frame).lift (wordTape k word) =
      Function.update (Sum.elim frame (fun _ => [])) (workerKey workers i k) word := by
  rw [wordTape, ← (layout workers i frame).update, layout_empty]
  rfl

end Holant.OneHot.StackProgram.Machine.Family
