import Holant.Proofs.Hardness.RealDenseSignTwist

/-! Three physical original-port orders put the unique asymmetric complementary
pair at 0011/1100. Every order fixes original port 0. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDensePortNormalize
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace A
export RealDenseCapClassification (sums differences BalancedCaps original_classification no_access_balanced)
end A
namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R

def order (i : Fin 3) : Equiv.Perm (Fin 4) where
  toFun := ![![0,1,2,3],![0,2,1,3],![0,3,2,1]] i
  invFun := ![![0,1,2,3],![0,2,1,3],![0,3,2,1]] i
  left_inv := by fin_cases i <;> decide
  right_inv := by fin_cases i <;> decide

variable {K : Type*} [Field K]
def normalized (M : Signature K 4) (i : Fin 3) : Signature K 4 := Tensor.reindex (order i) M

theorem normalized_entries (M : Signature K 4) (i : Fin 3) :
    entries (normalized M i)=
      ![entries M,
        ⟨(entries M).a,(entries M).c,(entries M).b,(entries M).d,
          (entries M).w,(entries M).y,(entries M).z,(entries M).x⟩,
        ⟨(entries M).a,(entries M).d,(entries M).c,(entries M).b,
          (entries M).y,(entries M).z,(entries M).w,(entries M).x⟩] i := by
  fin_cases i <;> apply Entries.ext
  all_goals apply congrArg M; funext k; fin_cases k <;> rfl

private theorem order_weight : ∀i (x : Word),weight (fun k=>x (order i k))=weight x := by decide

theorem eo (M : Signature K 4) (h : DenseEOUnitLocal.EOSupport M) (i : Fin 3) :
    DenseEOUnitLocal.EOSupport (normalized M i) := by
  intro x hx
  apply h
  simpa only [order_weight] using hx

theorem middle (M : Signature K 4) (h : DenseEOUnitLocal.NonzeroMiddle M) (i : Fin 3) :
    DenseEOUnitLocal.NonzeroMiddle (normalized M i) := by
  unfold DenseEOUnitLocal.NonzeroMiddle at *
  rw [normalized_entries]
  fin_cases i <;> dsimp at * <;> tauto

def network (M : Signature K 4) (i : Fin 3) : Network K 4 :=
  R.reindex (Network.corolla M) (order i)

theorem denote (M : Signature K 4) (i : Fin 3) : (network M i).denote=normalized M i := by
  rw [network,R.reindex_denote,Network.denote_corolla]
  rfl

def labels (M : Signature K 4) (i : Fin 3) : Labelling (network M i).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity _ := rfl
  edge := Fin.elim0
abbrev template (M : Signature K 4) (i : Fin 3) := (labels M i).template

theorem valid (M : Signature K 4) (i : Fin 3) :
    (template M i).WellFormed 1 1 (fun _=>4) := (labels M i).wellFormed

def ports (i : Fin 3) : List (ℕ ⊕ (ℕ × Bool)) :=
  ![[.inl 0,.inl 1,.inl 2,.inl 3],[.inl 0,.inl 2,.inl 1,.inl 3],
    [.inl 0,.inl 3,.inl 2,.inl 1]] i

theorem records (M : Signature K 4) (i : Fin 3) :
    (template M i).boundary=4 ∧ (template M i).vertices=[(0,ports i)] ∧
      (template M i).edges=[] := by
  fin_cases i <;> exact ⟨rfl,rfl,rfl⟩

theorem counts (M : Signature K 4) (i : Fin 3) :
    (template M i).vertices.length=1 ∧ (template M i).edges.length=0 := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem template_denote (M : Signature K 4) (i : Fin 3) :
    ((template M i).network (valid M i) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=normalized M i := by
  rw [←denote M i]
  apply Labelling.denote_template_of_labels (labels M i) _ _ (network M i).vertex (network M i).edge
  · intro v x; rfl
  · intro e; exact Fin.elim0 e

/-- The exceptional coefficient shape is a consequence of the six cap tests. -/
theorem exceptional (M : Signature ℝ 4) (i : Fin 3)
    (hi : A.differences M i≠0)
    (h : ∀j,j≠i → A.differences M j=0 ∧ A.sums M j= -A.sums M i) :
    RealDenseSignTwist.Exceptional (normalized M i) := by
  fin_cases i
  · have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    dsimp [A.differences,A.sums] at hi h1 h2
    constructor <;> rw [normalized_entries] <;> dsimp
    all_goals first | linarith | exact sub_ne_zero.mp hi
  · have h0 := h 0 (by decide)
    have h2 := h 2 (by decide)
    dsimp [A.differences,A.sums] at hi h0 h2
    constructor <;> rw [normalized_entries] <;> dsimp
    all_goals first | linarith | exact sub_ne_zero.mp hi
  · have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    dsimp [A.differences,A.sums] at hi h0 h1
    constructor <;> rw [normalized_entries] <;> dsimp
    all_goals first | linarith | exact sub_ne_zero.mp hi

theorem selfdual_original (M : Signature ℝ 4) (he : DenseEOUnitLocal.EOSupport M)
    (h : ∀i,A.differences M i=0) :
    M=ThreeModeSignatures.original (entries M).b (entries M).d (entries M).c := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  dsimp [A.differences] at h0 h1 h2
  have hy := sub_eq_zero.mp h0
  have hz := sub_eq_zero.mp h1
  have hw := sub_eq_zero.mp h2
  have hc := DenseEOUnitLocal.corners_zero M he
  have ht : entries M=⟨0,(entries M).b,(entries M).c,(entries M).d,
      (entries M).d,(entries M).c,(entries M).b,0⟩ := by
    ext <;> simp only [hc.1,hc.2,←hy,←hz,←hw]
  calc
    M=table (entries M) := (table_entries M (DenseEOUnitLocal.even M he)).symm
    _=ThreeModeSignatures.original (entries M).b (entries M).d (entries M).c := by
      conv_lhs => rw [ht]
      rfl

theorem antiselfdual_applicable (M : Signature ℝ 4)
    (he : DenseEOUnitLocal.EOSupport M) (hm : DenseEOUnitLocal.NonzeroMiddle M)
    (h : ∀i,A.sums M i=0) : AntiselfdualNormalize.Applicable M := by
  refine ⟨he,?_,hm.1,hm.2.1,hm.2.2.1⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  dsimp [A.sums] at h0 h1 h2
  have hy : (entries M).y= -(entries M).b := by linarith
  have hz : (entries M).z= -(entries M).c := by linarith
  have hw : (entries M).w= -(entries M).d := by linarith
  have hc := DenseEOUnitLocal.corners_zero M he
  intro x
  have ht := table_entries M (DenseEOUnitLocal.even M he)
  rw [←congrFun ht (fun i=>!x i),←congrFun ht x]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [table,h0,h1,h2,h3,hc.1,hc.2,hy,hz,hw]

/-- All real dense EO inputs reach an existing cap regime, a literal selfdual
triple, the accepted antiselfdual normalization, or the bounded exceptional
sign-twist construction. No hard endpoint is assumed in this classification. -/
theorem classification (M : Signature ℝ 4)
    (he : DenseEOUnitLocal.EOSupport M) (hm : DenseEOUnitLocal.NonzeroMiddle M) :
    GeneralCancellationCapPin.Applicable M ∨ GeneralGeometricCapLocal.Applicable M ∨
      M=ThreeModeSignatures.original (entries M).b (entries M).d (entries M).c ∨
      AntiselfdualNormalize.Applicable M ∨
      ∃i,RealDenseSignTwist.Exceptional (normalized M i) := by
  by_cases hd : GeneralCancellationCapPin.Applicable M
  · exact Or.inl hd
  by_cases hg : GeneralGeometricCapLocal.Applicable M
  · exact Or.inr (Or.inl hg)
  rcases A.original_classification M (A.no_access_balanced M hd hg) with hs|ha|⟨i,hi,h⟩
  · exact Or.inr (Or.inr (Or.inl (selfdual_original M he hs)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (antiselfdual_applicable M he hm ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i,exceptional M i hi h⟩)))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDensePortNormalize
