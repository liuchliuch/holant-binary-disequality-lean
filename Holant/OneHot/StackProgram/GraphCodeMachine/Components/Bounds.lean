import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Run
import Mathlib.Tactic.Linarith

namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
variable {A : Type} (e : Encoding A Bool) (C : ℕ)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A deliberately loose fixed constant covering both tree-compilation passes and
all descriptor and code-word framing. It depends only on the fixed label codec. -/
def descriptorRate (C : ℕ) : ℕ := 4 * rate C + 4 * overhead C + 100

def totalRate (C : ℕ) : ℕ := 2 * descriptorRate C + 17

@[simp] theorem chunk_append (left right : Code A) :
    chunk e (left ++ right) = chunk e left ++ chunk e right := records_append _ _ _

@[simp] theorem chunk_zero_length : (chunk e [.zero]).length = 8 := rfl
@[simp] theorem chunk_one_length : (chunk e [.one]).length = 8 := rfl
@[simp] theorem chunk_add_length : (chunk e [.swap, .add]).length = 16 := rfl
@[simp] theorem chunk_mul_length : (chunk e [.swap, .mul]).length = 16 := rfl

variable [Fintype A]
variable (hlabels : ∀ x, (e.encode x).length ≤ C)
include hlabels

theorem closedTime_le (root : A) (children : Forest A) :
    closedTime e root children ≤ rate C * ((closedEncoding e).encode (root, children)).length + overhead C := by
  simpa [closedTime, closedEncoding, FixedFieldMachines.pairEncoding, TreeEncoding.forestEncoding] using
    closed_time_le e C hlabels root children

theorem closed_chunk_le (root : A) (children : Forest A) :
    (chunk e (compileClosed root children)).length ≤
      rate C * ((closedEncoding e).encode (root, children)).length + overhead C := by
  have h := closedTime_le e C hlabels root children
  simp only [closedTime, code_records, List.length_append, List.length_singleton] at h
  unfold chunk
  omega

theorem descriptor_time_le (d : Descriptor A) :
    descriptorTicks e d ≤ descriptorRate C * (encode e d).length := by
  cases d with
  | dense => simp [descriptorTicks, bodyTicks, encode, descriptorRate]; omega
  | tree root children =>
    have ht := closedTime_le e C hlabels root children
    have ho := closed_chunk_le e C hlabels root children
    simp only [descriptorTicks, bodyTicks, encode, List.length_append, List.length_cons,
      List.length_nil, Holant.Algebraic.frame_length]
    unfold descriptorRate
    nlinarith
  | unicycle root children other forest =>
    have ht := closedTime_le e C hlabels root children
    have ho := closed_chunk_le e C hlabels root children
    have hu := closedTime_le e C hlabels other forest
    have hv := closed_chunk_le e C hlabels other forest
    simp only [descriptorTicks, bodyTicks, encode, List.length_append, List.length_cons,
      List.length_nil, Holant.Algebraic.frame_length]
    unfold descriptorRate
    nlinarith

theorem component_length_le (d : Descriptor A) :
    (chunk e (componentCode d)).length ≤ descriptorRate C * (encode e d).length := by
  cases d with
  | dense => simp [componentCode, encode, descriptorRate]; omega
  | tree root children =>
    have ho := closed_chunk_le e C hlabels root children
    simp only [componentCode, encode, List.length_append, List.length_cons,
      List.length_nil, Holant.Algebraic.frame_length]
    unfold descriptorRate
    nlinarith
  | unicycle root children other forest =>
    have ho := closed_chunk_le e C hlabels root children
    have hv := closed_chunk_le e C hlabels other forest
    simp only [componentCode, addCode, chunk_append, List.length_append, chunk_add_length,
      encode, List.length_cons, List.length_nil, Holant.Algebraic.frame_length]
    unfold descriptorRate
    nlinarith

def payloadSize (ds : List (Descriptor A)) : ℕ := (ds.map (fun d => (encode e d).length)).sum

theorem list_time_le (ds : List (Descriptor A)) :
    listTicks e ds ≤ descriptorRate C * payloadSize e ds := by
  induction ds with
  | nil => simp [listTicks, payloadSize]
  | cons d ds ih =>
    have h := descriptor_time_le e C hlabels d
    simp only [listTicks, payloadSize, List.map_cons, List.sum_cons] at *
    nlinarith

theorem chunks_length_le (ds : List (Descriptor A)) :
    (chunk e (ds.flatMap componentCode)).length ≤ descriptorRate C * payloadSize e ds := by
  induction ds with
  | nil => simp [chunk, records, payloadSize]
  | cons d ds ih =>
    have h := component_length_le e C hlabels d
    simp only [List.flatMap_cons, chunk_append, List.length_append, payloadSize,
      List.map_cons, List.sum_cons] at *
    nlinarith

omit hlabels [Fintype A] in
theorem input_length (ds : List (Descriptor A)) :
    ((listEncoding e).encode ds).length = 2 * payloadSize e ds + 2 * ds.length + 1 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [listEncoding, framedListEncoding, framedListEncode, List.length_cons,
      List.length_append, Holant.Algebraic.frame_length, encoding] at *
    simp only [payloadSize, List.map_cons, List.sum_cons] at *
    omega

omit hlabels [Fintype A] in
theorem output_length (ds : List (Descriptor A)) :
    ((codeEncoding e).encode (productCode ds)).length =
      (chunk e (ds.flatMap componentCode)).length + 16 * ds.length + 9 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [chunk] at ih ⊢
    simp only [productCode, mulCode, code_records, records_append, List.length_append,
      List.flatMap_cons, List.length_cons] at *
    have hm : (records (opEncoding e) [.swap, .mul]).length = 16 := rfl
    omega

/-- A linear bound in actual descriptor-list input bits, including fixed chunks,
all compiler calls, count manipulation, and final clean output reversal. -/
theorem total_time_le (ds : List (Descriptor A)) :
    listTicks e ds + ds.length + ((codeEncoding e).encode (productCode ds)).length + 6 ≤
      totalRate C * ((listEncoding e).encode ds).length + 15 := by
  have ht := list_time_le e C hlabels ds
  have ho := chunks_length_le e C hlabels ds
  rw [output_length, input_length]
  unfold totalRate
  nlinarith

end Holant.OneHot.StackProgram.GraphCodeMachine.Components
