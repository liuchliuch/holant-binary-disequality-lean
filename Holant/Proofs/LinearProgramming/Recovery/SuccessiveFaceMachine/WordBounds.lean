import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.Semantics

set_option autoImplicit false

/-! Kernel-checked recovery component. Direct byte accounting of appended rows, rather than
iterating a generic polynomial output bound n times. Even an infeasible face
returns only a box scalar with denominator<=ORIGINAL D, or the literal zero
fallback on an eager unused branch. Thus each actual row adds O(L^3) bits.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace WordBounds
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines Codec

def entryBits (L : ℕ) : ℕ := 2*L^2+2
def rowBits (L : ℕ) : ℕ := L*(2*entryBits L+2)+1
def increment (L : ℕ) : ℕ := 4*rowBits L+2*entryBits L+8
def scalarBits (L : ℕ) : ℕ := 4*L^2+4

theorem append_length {A : Type} (e : Encoding A Bool) (xs : List A) (a : A) :
    ((framedListEncoding e).encode (xs++[a])).length=
      ((framedListEncoding e).encode xs).length+2*(e.encode a).length+2 := by
  induction xs with
  | nil => simp [framedListEncoding,framedListEncode,frame_length]; omega
  | cons x xs ih =>
    simp only [List.cons_append,framedListEncoding,framedListEncode,List.length_cons,
      List.length_append,frame_length] at ih ⊢
    omega
theorem list_length {A : Type} (e : Encoding A Bool) (xs : List A) (B : ℕ)
    (h : ∀ a∈xs, (e.encode a).length≤B) :
    ((framedListEncoding e).encode xs).length≤xs.length*(2*B+2)+1 := by
  induction xs with
  | nil => simp [framedListEncoding,framedListEncode]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro a ha; exact h a (by simp [ha]))
    simp only [framedListEncoding,framedListEncode,List.length_cons,List.length_append,frame_length] at ht ⊢
    nlinarith
theorem integer_word (d : Raw) (z : ℤ) (hz : z.natAbs≤InputBounds.denominator d) :
    (IntegerArithmetic.encoding.encode z).length≤entryBits (InputBounds.size d) := by
  have hc := intCode_size_le z
  have hm := Nat.size_le_size hz
  have hd : (InputBounds.denominator d).size=2*InputBounds.size d^2+1 := by
    simp [InputBounds.denominator,Nat.size_pow]
  change (encodeNat (Equiv.intEquivNat z)).length≤_
  rw [encodeNat_length]
  unfold entryBits
  omega
theorem selected_bounds (c : Context) :
    0≤(Scalar.value c).getD 0 ∧ (Scalar.value c).getD 0≤1 ∧
      ((Scalar.value c).getD 0).den≤InputBounds.denominator c.original.val := by
  cases h : Scalar.value c with
  | none =>
    have hp := InputBounds.denominator_pos c.original.val
    simp only [Option.getD_none,Rat.den_zero]
    exact ⟨le_rfl,by norm_num,by omega⟩
  | some r => simpa only [Option.getD_some] using Scalar.returned_bounds c r h
theorem selected_word (c : Context) :
    (rationalEncoding.encode ((Scalar.value c).getD 0)).length≤scalarBits (InputBounds.size c.original.val) := by
  have hb := selected_bounds c
  have hn := ExactPointRecovery.Denominator.box_numerator ((Scalar.value c).getD 0) ⟨hb.1,hb.2.1⟩
  have hh : rationalHeight ((Scalar.value c).getD 0)≤InputBounds.denominator c.original.val :=
    max_le (hn.trans hb.2.2) hb.2.2
  have hm := Nat.size_le_size hh
  have hd : (InputBounds.denominator c.original.val).size=2*InputBounds.size c.original.val^2+1 := by
    simp [InputBounds.denominator,Nat.size_pow]
  have hw := rationalEncoding_length_le_height ((Scalar.value c).getD 0)
  unfold rationalBitHeight at hw
  unfold scalarBits
  omega

theorem front_word (c : Context) (r : ℚ) (hr : r.den≤InputBounds.denominator c.original.val) :
    (rowEncoding.encode (ExactPointRecovery.ThresholdProgram.front
      (c.current.1.val,c.current.2.val,r.num.toNat,r.den))).length≤rowBits (InputBounds.size c.original.val) := by
  have hn : c.current.1.val.dimension≤InputBounds.size c.original.val := by
    rw [c.sameDimension]
    exact InputBounds.dimension_le c.original.val
  have hcell : ∀ z∈ExactPointRecovery.ThresholdProgram.front
      (c.current.1.val,c.current.2.val,r.num.toNat,r.den),
      (IntegerArithmetic.encoding.encode z).length≤entryBits (InputBounds.size c.original.val) := by
    intro z hz
    simp only [ExactPointRecovery.ThresholdProgram.front,List.mem_map] at hz
    obtain ⟨i,hi,rfl⟩ := hz
    split
    · exact integer_word c.original.val (r.den:ℤ) (by simpa using hr)
    · exact integer_word c.original.val 0 (by simp)
  have hl := list_length IntegerArithmetic.encoding _ _ hcell
  have hs : (ExactPointRecovery.ThresholdProgram.front
      (c.current.1.val,c.current.2.val,r.num.toNat,r.den)).length=c.current.1.val.dimension := by
    simp [ExactPointRecovery.ThresholdProgram.front]
  rw [hs] at hl
  exact hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)

theorem fixation_increment (c : Context) (r : ℚ) (hr : 0≤r ∧ r≤1 ∧
    r.den≤InputBounds.denominator c.original.val) :
    InputBounds.size (c.next r).current.1.val≤InputBounds.size c.current.1.val+
      increment (InputBounds.size c.original.val) := by
  have hn := ExactPointRecovery.Denominator.box_numerator r ⟨hr.1,hr.2.1⟩
  have hnat : r.num.toNat=r.num.natAbs := by
    have hz := Rat.num_nonneg.mpr hr.1
    exact_mod_cast (Int.toNat_of_nonneg hz).trans (Int.natAbs_of_nonneg hz).symm
  have hp := integer_word c.original.val (r.num.toNat:ℤ) (by
    change r.num.toNat ≤ InputBounds.denominator c.original.val
    rw [hnat]
    exact hn.trans hr.2.2)
  have hrow := front_word c r hr.2.2
  have hrows : (rowsEncoding.encode (c.current.1.val.rows++[
      ExactPointRecovery.ThresholdProgram.front (c.current.1.val,c.current.2.val,r.num.toNat,r.den)])).length=
      (rowsEncoding.encode c.current.1.val.rows).length+
        2*(rowEncoding.encode (ExactPointRecovery.ThresholdProgram.front
          (c.current.1.val,c.current.2.val,r.num.toNat,r.den))).length+2 :=
    append_length rowEncoding c.current.1.val.rows
      (ExactPointRecovery.ThresholdProgram.front (c.current.1.val,c.current.2.val,r.num.toNat,r.den))
  have hrhs : (rowEncoding.encode (c.current.1.val.rhs++[(r.num.toNat:ℤ)])).length=
      (rowEncoding.encode c.current.1.val.rhs).length+
        2*(IntegerArithmetic.encoding.encode (r.num.toNat:ℤ)).length+2 :=
    append_length IntegerArithmetic.encoding c.current.1.val.rhs (r.num.toNat:ℤ)
  rw [InputBounds.length_formula,InputBounds.length_formula]
  change 2*(c.current.1.val.rowCount+1)+2*c.current.1.val.dimension+
      2*(rowsEncoding.encode (c.current.1.val.rows++[_])).length+
      (rowEncoding.encode (c.current.1.val.rhs++[_])).length+3≤_
  rw [hrows,hrhs]
  unfold increment
  omega
theorem advance_face (p : Payload) :
    InputBounds.size (context (advance p)).current.1.val≤InputBounds.size (context p).current.1.val+
      increment (InputBounds.size (context p).original.val) := by
  have h := fixation_increment (context p) ((Scalar.value (context p)).getD 0) (selected_bounds (context p))
  unfold advance cell update
  split <;> try split
  · exact h
  · simp only [context]; omega
  · simp only [context]; omega
theorem face_at (d : Input) (k : ℕ) :
    InputBounds.size (context («at» d k)).current.1.val≤InputBounds.size d.val.val+
      k*increment (InputBounds.size d.val.val) := by
  induction k with
  | zero => simp [«at»,initialPayload,initialContext,Context.initial,context]
  | succ k ih =>
    have ha := advance_face («at» d k)
    rw [Semantics.original_at] at ha
    change InputBounds.size (context (advance («at» d k))).current.1.val≤_
    nlinarith

theorem advance_points (p : Payload) : (points (advance p)).length≤(points p).length+1 := by
  unfold advance cell update
  split
  · split <;> simp [points]
  · simp [points]
theorem point_count (d : Input) (k : ℕ) : (points («at» d k)).length≤k := by
  induction k with
  | zero => simp [«at»,initialPayload,points]
  | succ k ih =>
    exact (advance_points («at» d k)).trans (Nat.add_le_add_right ih 1)
theorem point_words (d : Input) (k : ℕ) : ∀ r∈points («at» d k),
    (rationalEncoding.encode r).length≤scalarBits (InputBounds.size d.val.val) := by
  induction k with
  | zero => simp [«at»,initialPayload,points]
  | succ k ih =>
    have hw := selected_word (context («at» d k))
    rw [Semantics.original_at] at hw
    change ∀ r∈points (advance («at» d k)), _
    unfold advance cell update
    split <;> try split
    · intro r hr
      simp only [points,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hr
      rcases hr with hr | rfl
      · exact ih r hr
      · exact hw
    · exact ih
    · exact ih
theorem prefix_word (d : Input) (k : ℕ) :
    (Codec.pointEncoding.encode (points («at» d k))).length≤k*(2*scalarBits (InputBounds.size d.val.val)+2)+1 :=
  (list_length rationalEncoding _ _ (point_words d k)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (point_count d k)) 1)
end WordBounds
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
