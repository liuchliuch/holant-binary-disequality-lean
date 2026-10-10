import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists
import Holant.Complexity.FixedFieldMachines.PrimitiveCost
import Holant.OneHot.StackProgram.Machine.Dispatch

/-!
Physical framed-list fold with a genuinely finite accumulator. A bounded prefix
decision tree consumes exactly one fixed-width framed symbol and leaves the
remaining list on tape. No host fold, table lookup, or residue oracle is a TM2
instruction. This is used for binary parities, Z/4 sums, and row predicates.
-/

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.FiniteFold

open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing StackProtocol
open Turing.TM2.Stmt

variable {A S : Type} [Fintype A] [Fintype S]

/-- Unlike an EOF decoder this consumes a fixed prefix and preserves suffix. -/
def readPrefix {K Λ τ : Type} (src : K) (leaf : List Bool → Λ) :
    ℕ → List Bool → Stmt K Λ τ
  | 0, pre => load (fun v => (none, v.2)) (goto (fun _ => leaf pre))
  | n + 1, pre => pop src (fun v b => (b, v.2))
      (branch (fun v => v.1.getD false)
        (readPrefix src leaf n (pre ++ [true])) (readPrefix src leaf n (pre ++ [false])))

theorem prefix_exact {K Λ τ : Type} [DecidableEq K] (src : K) (leaf : List Bool → Λ)
    (n : ℕ) (pre word rest : List Bool) (hw : word.length = n)
    (v : Option Bool × τ) (tapes : K → List Bool) :
    TM2.stepAux (readPrefix src leaf n pre) v (Function.update tapes src (word ++ rest)) =
      cfg (leaf (pre ++ word)) v.2 (Function.update tapes src rest) := by
  induction n generalizing pre word v with
  | zero =>
    have he : word = [] := List.length_eq_zero_iff.mp hw
    subst word
    simp [readPrefix, TM2.stepAux, cfg]
  | succ n ih =>
    cases word with
    | nil => simp at hw
    | cons bit word =>
      have ht : word.length = n := by simpa using hw
      cases bit with
      | false =>
        simpa [readPrefix,TM2.stepAux,Function.update_idem,List.append_assoc] using
          (ih (pre ++ [false]) word ht (some false,v.2))
      | true =>
        simpa [readPrefix,TM2.stepAux,Function.update_idem,List.append_assoc] using
          (ih (pre ++ [true]) word ht (some true,v.2))

theorem prefix_budget {K Λ τ : Type} (src : K) (leaf : List Bool → Λ)
    (n : ℕ) (pre : List Bool) : TM2Cost.budget (readPrefix (τ := τ) src leaf n pre) ≤ 2 * n + 2 := by
  induction n generalizing pre with
  | zero => rfl
  | succ n ih =>
    simp only [readPrefix, TM2Cost.budget]
    have ht := ih (pre ++ [true])
    have hf := ih (pre ++ [false])
    omega

variable (ea : Encoding A Bool) (es : Encoding S Bool) (C : ℕ)
  (next : S → A → S) (initial : S)

def target (s : S) (bits : List Bool) : S :=
  match unframe bits with
  | none => s
  | some (word, _) => (ea.decode word).elim s (next s)

abbrev machine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := S
  main := initial
  State := Option Bool × Unit
  initial := (none, ())
  program s := pop () (fun v b => (b, v.2))
    (branch (fun v => v.1.getD false)
      (readPrefix () (target ea next s) (2 * C + 1) [])
      (load (fun v => (none, v.2)) (Constant.pushWord () (es.encode s) .halt)))

theorem entry_step (hc : ∀ a, (ea.encode a).length = C) (s : S) (a : A) (rest : List Bool) :
    (machine ea es C next initial).computer.step
      (cfg s () (wordTape () (true :: frame (ea.encode a) ++ rest))) =
      some (cfg (next s a) () (wordTape () rest)) := by
  have h := prefix_exact () (target ea next s) (2 * C + 1) [] (frame (ea.encode a)) rest
    (by simp [hc]) (some true, ()) (wordTape () [])
  have hf : unframe (frame (ea.encode a)) = some (ea.encode a,[]) := by
    simpa only [List.append_nil] using unframe_frame_append (ea.encode a) []
  change some (TM2.stepAux (readPrefix () (target ea next s) (2*C+1) [])
    (some true,()) (wordTape () (frame (ea.encode a) ++ rest))) = _
  apply congrArg some
  simpa only [List.nil_append,target,hf,ea.decode_encode,Option.elim_some,
    wordTape,Function.update_idem] using h

theorem finish_step (s : S) :
    (machine ea es C next initial).computer.step (cfg s () (wordTape () [false])) =
      some (haltList (machine ea es C next initial).computer (es.encode s)) := by
  rw [Machine.halt_eq]
  simp [machine, TM2.step, TM2.stepAux, cfg, wordTape, Constant.pushWord_eval]
  rfl

theorem run (hc : ∀ a, (ea.encode a).length = C) (xs : List A) (s : S) :
    RunsExactly (machine ea es C next initial).computer.step
      (cfg s () (wordTape () ((framedListEncoding ea).encode xs)))
      (haltList (machine ea es C next initial).computer (es.encode (xs.foldl next s))) (xs.length + 1) := by
  induction xs generalizing s with
  | nil => simpa [framedListEncoding, framedListEncode] using
      runsExactly_one (finish_step ea es C next initial s)
  | cons a xs ih =>
    simpa [framedListEncoding, framedListEncode, List.foldl_cons] using
      (runsExactly_one (entry_step ea es C next initial hc s a ((framedListEncoding ea).encode xs))).trans
        (ih (next s a))

noncomputable def computes (hc : ∀ a, (ea.encode a).length = C) :
    Computes (framedListEncoding ea) es (fun xs => xs.foldl next initial) where
  machine := machine ea es C next initial
  time := Polynomial.X + 1
  outputs xs := {
    steps := xs.length + 1
    evals_in_steps := by
      change RunsExactly (machine ea es C next initial).computer.step
        (initList (machine ea es C next initial).computer ((framedListEncoding ea).encode xs))
        (haltList (machine ea es C next initial).computer (es.encode (xs.foldl next initial)))
        (xs.length + 1)
      rw [Machine.init_eq]
      exact run ea es C next initial hc xs initial
    steps_le_m := by
      have h := framedListEncoding_length_lower ea xs
      simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
      omega }

theorem primitive_bound (hc : ∀ a, (ea.encode a).length = C) (xs : List A) :
    let w := computes ea es C next initial hc
    primitiveCost w.machine (w.outputs xs).steps
      (some (initList w.machine.computer ((framedListEncoding ea).encode xs))) ≤
        (primitivePolynomial w).eval ((framedListEncoding ea).encode xs).length :=
  computes_primitive_cost (computes ea es C next initial hc) xs

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.FiniteFold
