import Holant.Complexity.OracleBatch.Compose
import Holant.Complexity.OracleOneQuery.ContextReduction

namespace Holant.Complexity.OracleBatch
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic

/-- The public codec is exactly the established list encoding inside the
established pair encoding; arbitrary context follows the outer list frame. -/
def contextEncoding {γ ε : Type} (eq : Encoding γ Bool) (ee : Encoding ε Bool) :=
  pairEncoding (framedListEncoding eq) ee

@[simp] theorem list_encode {γ : Type} (eq : Encoding γ Bool) (qs : List γ) :
    (framedListEncoding eq).encode qs = listWord (qs.map eq.encode) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simpa only [framedListEncoding,framedListEncode,List.map_cons,listWord_cons] using
      congrArg (fun t => true :: (frame (eq.encode q) ++ t)) ih

@[simp] theorem context_encode {γ ε : Type} (eq : Encoding γ Bool) (ee : Encoding ε Bool) (v : List γ × ε) :
    (contextEncoding eq ee).encode v = word (v.1.map eq.encode) (ee.encode v.2) := by
  simp only [contextEncoding,pairEncoding,word,list_encode]

theorem member_length_le (qs : List (List Bool)) (q : List Bool) (hq : q ∈ qs) :
    q.length ≤ (listWord qs).length := by
  induction qs with
  | nil => simp at hq
  | cons r rs ih =>
    simp only [List.mem_cons] at hq
    simp only [listWord_cons,List.length_cons,List.length_append,frame_length]
    rcases hq with rfl | hq
    · omega
    · have := ih hq; omega

theorem list_length_le (qs : List (List Bool)) : qs.length ≤ (listWord qs).length := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [listWord_cons,List.length_cons,List.length_append,frame_length]
    omega

theorem listWord_length_le (qs : List (List Bool)) (bound : ℕ)
    (h : ∀ q ∈ qs, q.length ≤ bound) :
    (listWord qs).length ≤ (2 * bound + 2) * qs.length + 1 := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have hq := h q (by simp)
    have ht := ih (by intro r hr; exact h r (by simp [hr]))
    simp only [listWord_cons,List.length_cons,List.length_append,frame_length,Nat.mul_add,Nat.mul_one]
    omega

variable {α β γ δ ε : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {eq : Encoding γ Bool} {ed : Encoding δ Bool} {ee : Encoding ε Bool}
  {pre : α → List γ × ε} {post : List δ × ε → β} {g : γ → δ}

def answers (g : γ → δ) (v : List γ × ε) : List δ × ε := (v.1.map g,v.2)

noncomputable def answerBound (a : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq ed g) : Polynomial ℕ := size.bound.comp a.outputBound.bound

noncomputable def decoderBound (a : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq ed g) : Polynomial ℕ :=
  2 * ((2 * answerBound a size + 2) * a.outputBound.bound + 1) + 1 + a.outputBound.bound

theorem query_context_length_le (a : Computes ea (contextEncoding eq ee) pre) (x : α) :
    (listWord ((pre x).1.map eq.encode)).length ≤ a.outputBound.bound.eval (ea.encode x).length ∧
    (pre x).1.length ≤ a.outputBound.bound.eval (ea.encode x).length ∧
    (ee.encode (pre x).2).length ≤ a.outputBound.bound.eval (ea.encode x).length := by
  have h := a.outputBound.length_le x
  rw [context_encode] at h
  have hn := list_length_le ((pre x).1.map eq.encode)
  simp only [List.length_map] at hn
  simp only [word,List.length_append,frame_length] at h
  omega

theorem answer_length_le (a : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq ed g) (x : α) (q : γ) (hq : q ∈ (pre x).1) :
    (ed.encode (g q)).length ≤ (answerBound a size).eval (ea.encode x).length := by
  have hq' := member_length_le ((pre x).1.map eq.encode) (eq.encode q) (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hn := (query_context_length_le a x).1
  exact le_trans (size.length_le q) (by
    simpa [answerBound] using natPolynomial_eval_mono size.bound (le_trans hq' hn))

theorem decoder_length_le (a : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq ed g) (x : α) :
    ((contextEncoding ed ee).encode (answers g (pre x))).length ≤
      (decoderBound a size).eval (ea.encode x).length := by
  have hl := listWord_length_le (((pre x).1.map g).map ed.encode)
    ((answerBound a size).eval (ea.encode x).length) (by
      intro q hq
      simp only [List.mem_map] at hq
      rcases hq with ⟨d,⟨q,hq,rfl⟩,rfl⟩
      exact answer_length_le a size x q hq)
  have hn := (query_context_length_le a x).2.1
  have hc := (query_context_length_le a x).2.2
  simp only [List.length_map] at hl
  have hm := Nat.mul_le_mul_left (2 * (answerBound a size).eval (ea.encode x).length + 2) hn
  simp only [context_encode,answers,word,List.length_append,frame_length,decoderBound,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

theorem oracle_encoded_list (oracle : List Bool → List Bool) (ho : RepresentsOracle eq ed g oracle)
    (qs : List γ) : (qs.map eq.encode).map oracle = (qs.map g).map ed.encode := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  exact ho q

end Holant.Complexity.OracleBatch
