import Holant.Proofs.Hardness.GeneralCancellationCapPin
import Holant.Proofs.Hardness.ThreeModeSignatures

/-! Actual two-original-M normalization of an antiselfdual EO signature.
The cap uses original loop 03 or 12, selected from b-c and b+c. Its second
boundary is connected through native X to original port 0 of another M.
The first cap boundary is output 0, followed by original M ports 1,2,3. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.AntiselfdualNormalize
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export GeneralCancellationCapPin (network full_table antiTensor coefficients)
end C
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote tensor tensor_denote)
end Chain
open Classical
variable {K : Type*} [Field K]

structure Applicable (M : Signature K 4) : Prop where
  eo : DenseEOUnitLocal.EOSupport M
  anti : ∀x, M (fun i=>!x i) = -M x
  nonzeroB : (entries M).b≠0
  nonzeroC : (entries M).c≠0
  nonzeroD : (entries M).d≠0

def normalized (M : Signature K 4) : Signature K 4 := fun x=>if x 0 then -M x else M x

theorem opposite (M : Signature K 4) (h : Applicable M) :
    (entries M).y= -(entries M).b ∧ (entries M).z= -(entries M).c ∧
      (entries M).w= -(entries M).d := by
  have hword (x : Fin 4→Bool) : (fun i=>!x i)=![!x 0,!x 1,!x 2,!x 3] := by
    funext i; fin_cases i <;> rfl
  constructor
  · simpa [hword,entries] using h.anti ![false,false,true,true]
  constructor
  · simpa [hword,entries] using h.anti ![false,true,false,true]
  · simpa [hword,entries] using h.anti ![false,true,true,false]

theorem normalized_eq (M : Signature K 4) (h : Applicable M) :
    normalized M=ThreeModeSignatures.original (entries M).b (entries M).d (entries M).c := by
  have ht := table_entries M (DenseEOUnitLocal.even M h.eo)
  have hz := DenseEOUnitLocal.corners_zero M h.eo
  have ho := opposite M h
  funext x
  change (if x 0 then -M x else M x)=_
  rw [←congrFun ht x]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [ThreeModeSignatures.original,table,h0,h1,h2,h3,hz.1,hz.2,ho.1,ho.2.1,ho.2.2]

theorem normalized_selfdual (M : Signature K 4) (h : Applicable M) (x : Fin 4→Bool) :
    normalized M (fun i=>!x i)=normalized M x := by
  rw [normalized_eq M h]
  exact ThreeModeSignatures.self_dual _ _ _ x

def choice (M : Signature K 4) : Fin 6 := if (entries M).b-(entries M).c≠0 then 2 else 3

def scale (M : Signature K 4) : K := if (entries M).b-(entries M).c≠0
  then (entries M).b-(entries M).c else (entries M).b+(entries M).c

theorem scale_nonzero [CharZero K] (M : Signature K 4) (h : Applicable M) : scale M≠0 := by
  unfold scale
  split_ifs with hn
  · exact hn
  · have he : (entries M).b=(entries M).c := sub_eq_zero.mp (not_ne_iff.mp hn)
    rw [←he]
    intro hz
    have : (2 : K)*(entries M).b=0 := by simpa only [two_mul] using hz
    exact h.nonzeroB ((mul_eq_zero.mp this).resolve_left (by norm_num))

theorem cap_value (M : Signature K 4) (h : Applicable M) :
    (C.network M (choice M,false)).denote=C.antiTensor (scale M) (-(scale M)) := by
  rw [C.full_table M (DenseEOUnitLocal.even M h.eo)]
  have ho := opposite M h
  unfold choice scale
  split_ifs <;> simp [GeneralCancellationCapPin.oriented,C.coefficients,ho.1,ho.2.1,ho.2.2,sub_eq_add_neg]

def attachOrder : Equiv.Perm (Fin 6) where
  toFun := ![2,0,1,3,4,5]
  invFun := ![1,2,0,3,4,5]
  left_inv := by decide
  right_inv := by decide

def capNetwork (M : Signature K 4) (k : Fin 6) : Network K 4 :=
  (Chain.reindex (Chain.tensor (C.network M (k,false)) (Network.corolla M)) attachOrder).contract Signature.disequality

def network (M : Signature K 4) : Network K 4 := capNetwork M (choice M)

theorem contraction (M : Signature K 4) (k : Fin 6) (x : Fin 4→Bool) :
    (capNetwork M k).denote x=
      (C.network M (k,false)).denote ![x 0,false]*M ![true,x 1,x 2,x 3]+
      (C.network M (k,false)).denote ![x 0,true]*M ![false,x 1,x 2,x 3] := by
  rw [capNetwork,Network.denote_contract,Chain.reindex_denote,Chain.tensor_denote,
    Network.denote_corolla,Signature.contract_disequality]
  have hc (a b : Bool) :
      (fun p : Fin 2 => (Fin.cons a (Fin.cons b x) : Fin 6→Bool) (attachOrder (Fin.castAdd 4 p)))=![x 0,a] := by
    funext p; fin_cases p <;> rfl
  have hm (a b : Bool) :
      (fun p : Fin 4 => (Fin.cons a (Fin.cons b x) : Fin 6→Bool) (attachOrder (Fin.natAdd 2 p)))=![b,x 1,x 2,x 3] := by
    funext p; fin_cases p <;> rfl
  simp only [Tensor.reindex_apply,Signature.tensor_apply,hc,hm]

theorem denote (M : Signature K 4) (h : Applicable M) :
    (network M).denote=scale M • normalized M := by
  funext x
  rw [network,contraction,cap_value M h]
  have hx : ![x 0,x 1,x 2,x 3]=x := by funext i; fin_cases i <;> rfl
  cases h0 : x 0 <;>
    simp [C.antiTensor,normalized,h0,Pi.smul_apply,smul_eq_mul]
  · have he : ![false,x 1,x 2,x 3]=x := by simpa only [h0] using hx
    simp only [he,eq_self,true_or]
  · have he : ![true,x 1,x 2,x 3]=x := by simpa only [h0] using hx
    simp only [he,eq_self,true_or]

def labels (M : Signature K 4) (k : Fin 6) : Labelling (capNetwork M k).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity v := by fin_cases v <;> rfl
  edge _ := 0

abbrev template (M : Signature K 4) (k : Fin 6) := (labels M k).template

theorem valid (M : Signature K 4) (k : Fin 6) :
    (template M k).WellFormed 1 1 (fun _=>4) := (labels M k).wellFormed

theorem records2 (M : Signature K 4) :
    (template M 2).boundary=4 ∧
    (template M 2).vertices=[
      (0,[.inr (1,false),.inl 0,.inr (0,false),.inr (1,true)]),
      (0,[.inr (0,true),.inl 1,.inl 2,.inl 3])] ∧
    (template M 2).edges=[0,0] := ⟨rfl,rfl,rfl⟩

theorem records3 (M : Signature K 4) :
    (template M 3).boundary=4 ∧
    (template M 3).vertices=[
      (0,[.inl 0,.inr (1,false),.inr (1,true),.inr (0,false)]),
      (0,[.inr (0,true),.inl 1,.inl 2,.inl 3])] ∧
    (template M 3).edges=[0,0] := ⟨rfl,rfl,rfl⟩

theorem counts (M : Signature K 4) :
    (template M (choice M)).vertices.length=2 ∧ (template M (choice M)).edges.length=2 := by
  unfold choice
  split_ifs <;> exact ⟨rfl,rfl⟩

theorem literal_vertex (M : Signature K 4) (k : Fin 6)
    (v : Fin (capNetwork M k).shape.vertices) :
    (⟨(capNetwork M k).shape.arity v,(capNetwork M k).vertex v⟩ : AnySignature K)=⟨4,M⟩ := by
  fin_cases v <;> rfl

theorem template_actual (M : Signature K 4) (k : Fin 6) :
    ((template M k).network (valid M k) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=(capNetwork M k).denote := by
  apply Labelling.denote_template_of_labels (labels M k) _ _ (capNetwork M k).vertex (capNetwork M k).edge
  · intro v x; fin_cases v <;> rfl
  · intro e a b; fin_cases e <;> rfl

theorem template_denote (M : Signature K 4) (h : Applicable M) :
    ((template M (choice M)).network (valid M (choice M)) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=scale M • normalized M := by
  rw [template_actual]
  exact denote M h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.AntiselfdualNormalize
