import Holant.Proofs.Hardness.ComplexNonselfdualCompression
import Holant.Proofs.Hardness.FiveSupportEOOrdering

/-! The twelve EO four-word masks whose missing words are not complementary.
A selected two-copy original-M/native-X network has exactly five nonzero entries.
The selection is by original coefficients; no gadget, basis or hardness is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseFourLocal
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace O
export FiveSupportEOOrdering (middleWord middleCoeff ExactlyFive)
end O
namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R
set_option backward.isDefEq.respectTransparency false

def MaskCondition (B : Fin 6 → Bool) : Prop :=
  (Finset.univ.filter fun i=>B i).card=4 ∧ ∀i, B i=false → B (5-i)=true
instance (B : Fin 6 → Bool) : Decidable (MaskCondition B) := by
  unfold MaskCondition
  infer_instance

def patterns : Fin 12 → Fin 6 → Bool := ![
    ![false,false,true,true,true,true],
    ![false,true,false,true,true,true],
    ![false,true,true,false,true,true],
    ![false,true,true,true,false,true],
    ![true,false,false,true,true,true],
    ![true,false,true,false,true,true],
    ![true,false,true,true,true,false],
    ![true,true,false,true,false,true],
    ![true,true,false,true,true,false],
    ![true,true,true,false,false,true],
    ![true,true,true,false,true,false],
    ![true,true,true,true,false,false]]

def forward : Fin 12 → Fin 4 → Fin 4 := ![
    ![1,2,3,0],
    ![1,2,0,3],
    ![2,1,3,0],
    ![2,1,0,3],
    ![1,0,2,3],
    ![2,3,1,0],
    ![2,0,1,3],
    ![2,3,0,1],
    ![2,0,3,1],
    ![0,1,2,3],
    ![0,2,1,3],
    ![0,2,3,1]]

def backward : Fin 12 → Fin 4 → Fin 4 := ![
    ![3,0,1,2],
    ![2,0,1,3],
    ![3,1,0,2],
    ![2,1,0,3],
    ![1,0,2,3],
    ![3,2,0,1],
    ![1,2,0,3],
    ![2,3,0,1],
    ![1,3,0,2],
    ![0,1,2,3],
    ![0,2,1,3],
    ![0,3,1,2]]

def middleMap : Fin 12 → Fin 6 → Fin 6 := ![
    ![2,4,5,0,1,3],
    ![1,3,5,0,2,4],
    ![4,2,5,0,3,1],
    ![3,1,5,0,4,2],
    ![0,3,4,1,2,5],
    ![5,2,4,1,3,0],
    ![3,0,4,1,5,2],
    ![5,1,3,2,4,0],
    ![4,0,3,2,5,1],
    ![0,1,2,3,4,5],
    ![1,0,2,3,5,4],
    ![2,0,1,4,5,3]]

private theorem inverse_left : ∀i x,backward i (forward i x)=x := by decide
private theorem inverse_right : ∀i x,forward i (backward i x)=x := by decide
def order (i : Fin 12) : Equiv.Perm (Fin 4) where
  toFun := forward i
  invFun := backward i
  left_inv := inverse_left i
  right_inv := inverse_right i

private theorem middle_map : ∀j i,(fun k=>O.middleWord i (order j k))=O.middleWord (middleMap j i) := by
  decide

def choose (B : Fin 6 → Bool) : Fin 12 :=
  if B=patterns 0 then 0 else
  if B=patterns 1 then 1 else
  if B=patterns 2 then 2 else
  if B=patterns 3 then 3 else
  if B=patterns 4 then 4 else
  if B=patterns 5 then 5 else
  if B=patterns 6 then 6 else
  if B=patterns 7 then 7 else
  if B=patterns 8 then 8 else
  if B=patterns 9 then 9 else
  if B=patterns 10 then 10 else 11

theorem twelve_patterns : ∀B,MaskCondition B ↔ ∃j,B=patterns j := by decide
theorem choose_pattern : ∀j,choose (patterns j)=j := by decide

theorem normalized_mask : ∀B,MaskCondition B →
    B (middleMap (choose B) 0)=true ∧ B (middleMap (choose B) 1)=true ∧
    B (middleMap (choose B) 2)=true ∧ B (middleMap (choose B) 3)=false ∧
    B (middleMap (choose B) 4)=false ∧ B (middleMap (choose B) 5)=true := by decide

variable {K : Type} [Field K]
def mask (M : Signature K 4) : Fin 6 → Bool := by
  classical
  exact fun i=>decide (O.middleCoeff M i≠0)
def Applicable (M : Signature K 4) : Prop := MaskCondition (mask M)
def index (M : Signature K 4) := choose (mask M)
def oriented (M : Signature K 4) (j : Fin 12) := Tensor.reindex (order j) M

theorem oriented_eo (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (j : Fin 12) :
    DenseEOUnitLocal.EOSupport (oriented M j) := by
  intro x hx
  apply he
  have hw : weight (fun k=>x (order j k))=weight x :=
    Equiv.sum_comp (order j) (fun k=>if x k then 1 else 0)
  simpa only [hw] using hx

omit [Field K] in
theorem oriented_middle (M : Signature K 4) (j : Fin 12) (i : Fin 6) :
    O.middleCoeff (oriented M j) i=O.middleCoeff M (middleMap j i) := by
  unfold O.middleCoeff oriented Tensor.reindex
  rw [middle_map]

theorem selected_coefficients (M : Signature K 4) (h : Applicable M) :
    (entries (oriented M (index M))).b≠0 ∧ (entries (oriented M (index M))).c≠0 ∧
    (entries (oriented M (index M))).d≠0 ∧ (entries (oriented M (index M))).w=0 ∧
    (entries (oriented M (index M))).z=0 ∧ (entries (oriented M (index M))).y≠0 := by
  classical
  have hm := normalized_mask (mask M) h
  change O.middleCoeff (oriented M (index M)) 0≠0 ∧ O.middleCoeff (oriented M (index M)) 1≠0 ∧
    O.middleCoeff (oriented M (index M)) 2≠0 ∧ O.middleCoeff (oriented M (index M)) 3=0 ∧
    O.middleCoeff (oriented M (index M)) 4=0 ∧ O.middleCoeff (oriented M (index M)) 5≠0
  simp only [oriented_middle]
  simpa only [mask,index,decide_eq_true_eq,decide_eq_false_iff_not,not_not] using hm

def swap : Equiv.Perm (Fin 4) where
  toFun := ![0,2,1,3]
  invFun := ![0,2,1,3]
  left_inv := by decide
  right_inv := by decide

def network (M : Signature K 4) (j : Fin 12) : Network K 4 :=
  let N := R.reindex (Network.corolla M) (order j)
  R.reindex (ExactTwoChain.series N (R.reindex N swap)) swap

def output (M : Signature K 4) (j : Fin 12) : Signature K 4 :=
  let e := entries (oriented M j)
  table ⟨0,e.b*e.c,e.c*e.d,e.d^2,e.c*e.y,e.d*e.y,0,0⟩

theorem denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (hs : Applicable M) :
    (network M (index M)).denote=output M (index M) := by
  have hn := selected_coefficients M hs
  have hz := DenseEOUnitLocal.corners_zero _ (oriented_eo M he (index M))
  have ht := table_entries (oriented M (index M)) (DenseEOUnitLocal.even _ (oriented_eo M he (index M)))
  funext x
  simp only [network,R.reindex_denote,Tensor.reindex_apply,ExactTwoChain.series_denote,Network.denote_corolla]
  have hv (a b c d : Bool) : (fun k=> (![a,b,c,d] : Fin 4→Bool) (swap k))=![a,c,b,d] := by
    funext k
    fin_cases k <;> rfl
  change (∑u : Bool, ∑v : Bool,
    oriented M (index M) ![x 0,u,x 1,v] *
      oriented M (index M) (fun k=> (![!u,x 2,!v,x 3] : Fin 4→Bool) (swap k)))=output M (index M) x
  simp only [hv]
  rw [←ht]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [table,swap,output,h0,h1,h2,h3,hz.1,hz.2,hn.2.2.2.1,hn.2.2.2.2.1]
  all_goals ring

theorem output_eo (M : Signature K 4) (j : Fin 12) : DenseEOUnitLocal.EOSupport (output M j) := by
  intro x hx
  rw [Holant.EightVertex.ProductAnchor.weight_four] at hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals try norm_num [h0,h1,h2,h3] at hx
  all_goals simp [output,table,h0,h1,h2,h3]

theorem output_five (M : Signature K 4) (hs : Applicable M) : O.ExactlyFive (output M (index M)) := by
  have hn := selected_coefficients M hs
  apply (FiveSupportEOOrdering.exactlyFive_iff _).mpr
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
  exact ⟨mul_ne_zero hn.1 hn.2.1,mul_ne_zero hn.2.1 hn.2.2.1,pow_ne_zero 2 hn.2.2.1,
    mul_ne_zero hn.2.1 hn.2.2.2.2.2,mul_ne_zero hn.2.2.1 hn.2.2.2.2.2,rfl⟩

def labels (M : Signature K 4) (j : Fin 12) : Labelling (network M j).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity v := by fin_cases v <;> rfl
  edge _ := 0
abbrev template (M : Signature K 4) (j : Fin 12) := (labels M j).template
theorem valid (M : Signature K 4) (j : Fin 12) :
    (template M j).WellFormed 1 1 (fun _=>4) := (labels M j).wellFormed
theorem counts (M : Signature K 4) (j : Fin 12) :
    (template M j).vertices.length=2 ∧ (template M j).edges.length=2 := ⟨rfl,rfl⟩
theorem template_denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (hs : Applicable M) :
    ((template M (index M)).network (valid M (index M)) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=output M (index M) := by
  rw [←denote M he hs]
  apply Labelling.denote_template_of_labels (labels M (index M)) _ _ (network M (index M)).vertex (network M (index M)).edge
  · intro v x; fin_cases v <;> rfl
  · intro e x y; fin_cases e <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseFourLocal
