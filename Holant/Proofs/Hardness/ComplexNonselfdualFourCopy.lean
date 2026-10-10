import Holant.Proofs.Hardness.ComplexNonselfdualCompression
import Holant.Proofs.Hardness.RealDensePortNormalize

/-! Four literal original occurrences suffice to make all opposite pairs
symmetric whenever the selected explicit pair-sum conditions hold. The choice
of a successful order is kept separate from the network semantics. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualFourCopy
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export ComplexNonselfdualCompression (compressed compressed_entries compressed_eo
  compressed_middle compressNetwork compressNetwork_denote)
end C
namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K]

def order (i : Fin 3) : Equiv.Perm (Fin 4) where
  toFun := ![![0,1,2,3],![0,2,1,3],![0,1,3,2]] i
  invFun := ![![0,1,2,3],![0,2,1,3],![0,1,3,2]] i
  left_inv := by fin_cases i <;> decide
  right_inv := by fin_cases i <;> decide

def oriented (M : Signature K 4) (i : Fin 3) : Signature K 4 := Tensor.reindex (order i) M

omit [Field K] in
theorem oriented_entries (M : Signature K 4) (i : Fin 3) :
    entries (oriented M i)=![entries M,
      ⟨(entries M).a,(entries M).c,(entries M).b,(entries M).d,
        (entries M).w,(entries M).y,(entries M).z,(entries M).x⟩,
      ⟨(entries M).a,(entries M).b,(entries M).d,(entries M).c,
        (entries M).z,(entries M).w,(entries M).y,(entries M).x⟩] i := by
  fin_cases i <;> apply Entries.ext
  all_goals apply congrArg M; funext k; fin_cases k <;> rfl

private theorem order_weight : ∀i (x : Word),weight (fun k=>x (order i k))=weight x := by decide

theorem oriented_eo (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 3) :
    DenseEOUnitLocal.EOSupport (oriented M i) := by
  intro x hx
  apply he
  simpa only [order_weight] using hx

theorem oriented_middle (M : Signature K 4) (hm : DenseEOUnitLocal.NonzeroMiddle M) (i : Fin 3) :
    DenseEOUnitLocal.NonzeroMiddle (oriented M i) := by
  unfold DenseEOUnitLocal.NonzeroMiddle at *
  rw [oriented_entries]
  fin_cases i <;> dsimp at * <;> tauto

def first (M : Signature K 4) (i : Fin 3) : Network K 4 :=
  C.compressNetwork (R.reindex (Network.corolla M) (order i))
def middle (M : Signature K 4) (i : Fin 3) : Signature K 4 :=
  oriented (C.compressed (oriented M i)) 1
def network (M : Signature K 4) (i : Fin 3) : Network K 4 :=
  C.compressNetwork (R.reindex (first M i) (order 1))
def output (M : Signature K 4) (i : Fin 3) : Signature K 4 := C.compressed (middle M i)

theorem first_denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 3) :
    (first M i).denote=C.compressed (oriented M i) := by
  apply C.compressNetwork_denote
  · rw [R.reindex_denote,Network.denote_corolla]; rfl
  · exact oriented_eo M he i

theorem denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 3) :
    (network M i).denote=output M i := by
  apply C.compressNetwork_denote
  · rw [R.reindex_denote,first_denote M he i]; rfl
  · exact oriented_eo _ (C.compressed_eo _) 1

def isolated (M : Signature K 4) (i : Fin 3) : K :=
  (entries (oriented M i)).c*(entries (oriented M i)).z

def pairSum (M : Signature K 4) (i : Fin 3) : K :=
  (entries (oriented M i)).b*(entries (oriented M i)).y+
    (entries (oriented M i)).d*(entries (oriented M i)).w

theorem isolated_values (M : Signature K 4) (i : Fin 3) :
    isolated M i=![(entries M).c*(entries M).z,(entries M).b*(entries M).y,
      (entries M).d*(entries M).w] i := by
  unfold isolated
  rw [oriented_entries]
  fin_cases i <;> rfl

theorem pairSum_values (M : Signature K 4) (i : Fin 3) :
    pairSum M i=![(entries M).b*(entries M).y+(entries M).d*(entries M).w,
      (entries M).c*(entries M).z+(entries M).d*(entries M).w,
      (entries M).b*(entries M).y+(entries M).c*(entries M).z] i := by
  unfold pairSum
  rw [oriented_entries]
  fin_cases i <;> rfl

def totalProduct (M : Signature K 4) : K :=
  (entries M).b*(entries M).d*(entries M).w*(entries M).y

/-- The asymmetric entries multiply together in the second stage. -/
theorem output_entries (M : Signature K 4) (i : Fin 3) :
    entries (output M i)=
      ⟨0,2*isolated M i*pairSum M i,
        4*(entries (oriented M i)).b*(entries (oriented M i)).d*
          (entries (oriented M i)).w*(entries (oriented M i)).y,
        isolated M i^2+pairSum M i^2,isolated M i^2+pairSum M i^2,
        4*(entries (oriented M i)).b*(entries (oriented M i)).d*
          (entries (oriented M i)).w*(entries (oriented M i)).y,
        2*isolated M i*pairSum M i,0⟩ := by
  dsimp only [isolated,pairSum]
  simp only [output,C.compressed_entries,middle,oriented_entries]
  ext <;> dsimp <;> ring

theorem output_eo (M : Signature K 4) (i : Fin 3) : DenseEOUnitLocal.EOSupport (output M i) :=
  C.compressed_eo _

theorem output_opposite (M : Signature K 4) (i : Fin 3) :
    (entries (output M i)).b=(entries (output M i)).y ∧
    (entries (output M i)).d=(entries (output M i)).w ∧
    (entries (output M i)).c=(entries (output M i)).z := by
  rw [output_entries]
  exact ⟨rfl,rfl,rfl⟩

theorem output_middle [CharZero K] (M : Signature K 4)
    (hm : DenseEOUnitLocal.NonzeroMiddle M) (i : Fin 3)
    (hs : pairSum M i≠0) (hq : isolated M i^2+pairSum M i^2≠0) :
    DenseEOUnitLocal.NonzeroMiddle (output M i) := by
  have ho := oriented_middle M hm i
  rcases ho with ⟨hb,hc,hd,hw,hz,hy⟩
  have ht : isolated M i≠0 := mul_ne_zero hc hz
  unfold DenseEOUnitLocal.NonzeroMiddle
  rw [output_entries]
  exact ⟨mul_ne_zero (mul_ne_zero (by norm_num) ht) hs,
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb) hd) hw) hy,
    hq,hq,mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hb) hd) hw) hy,
    mul_ne_zero (mul_ne_zero (by norm_num) ht) hs⟩

def labels (M : Signature K 4) (i : Fin 3) : Labelling (network M i).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity v := by fin_cases v <;> rfl
  edge _ := 0
abbrev template (M : Signature K 4) (i : Fin 3) := (labels M i).template

theorem valid (M : Signature K 4) (i : Fin 3) : (template M i).WellFormed 1 1 (fun _=>4) :=
  (labels M i).wellFormed

theorem counts (M : Signature K 4) (i : Fin 3) :
    (template M i).vertices.length=4 ∧ (template M i).edges.length=6 := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

/-- Ordered original rows, including the six separately indexed native edges. -/
def rows (i : Fin 3) : List (ℕ × List (ℕ ⊕ (ℕ × Bool))) := ![
  [(0,[.inl 0,.inr (3,false),.inr (1,false),.inr (2,false)]),
   (0,[.inl 2,.inr (3,true),.inr (0,false),.inr (2,true)]),
   (0,[.inl 1,.inr (5,false),.inr (1,true),.inr (4,false)]),
   (0,[.inl 3,.inr (5,true),.inr (0,true),.inr (4,true)])],
  [(0,[.inl 0,.inr (1,false),.inr (3,false),.inr (2,false)]),
   (0,[.inl 2,.inr (0,false),.inr (3,true),.inr (2,true)]),
   (0,[.inl 1,.inr (1,true),.inr (5,false),.inr (4,false)]),
   (0,[.inl 3,.inr (0,true),.inr (5,true),.inr (4,true)])],
  [(0,[.inl 0,.inr (3,false),.inr (2,false),.inr (1,false)]),
   (0,[.inl 2,.inr (3,true),.inr (2,true),.inr (0,false)]),
   (0,[.inl 1,.inr (5,false),.inr (4,false),.inr (1,true)]),
   (0,[.inl 3,.inr (5,true),.inr (4,true),.inr (0,true)])]] i


theorem records (M : Signature K 4) (i : Fin 3) :
    (template M i).boundary=4 ∧ (template M i).vertices=rows i ∧
      (template M i).edges=[0,0,0,0,0,0] := by
  fin_cases i <;> exact ⟨rfl,rfl,rfl⟩

theorem template_denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 3) :
    ((template M i).network (valid M i) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=output M i := by
  rw [←denote M he i]
  apply Labelling.denote_template_of_labels (labels M i) _ _ (network M i).vertex (network M i).edge
  · intro v x; fin_cases i <;> fin_cases v <;> rfl
  · intro e x y; fin_cases i <;> fin_cases e <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualFourCopy
