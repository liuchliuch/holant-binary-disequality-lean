import Holant.Proofs.Reductions.EightVertexNonexception.NativeChain
import Holant.Proofs.Hardness.LabelledNetwork

/-!
# One-copy original sparse M gives a literal directed 01 pin

The sole native-X loop joins ORIGINAL ports zero and two. Remaining boundary
order is [3,1]. The actual two-term contraction is M[0,t1,1,t0]+M[1,t1,0,t0].
For the ORIGINAL sparse coefficients b=y=w=0 it is exactly d times 01.
No spectral assumption, interpolation, unary label, free wire or hardness
statement is supplied. Loops and ordered ports are the actual network model.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseDirectPin
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end Chain
variable {K : Type*} [Field K]

def portOrder : Equiv.Perm (Fin 4) where
  toFun := ![0,3,1,2]
  invFun := ![0,2,3,1]
  left_inv := by decide
  right_inv := by decide

def network (M : Signature K 4) : Network K 2 :=
  (Chain.reindex (Network.corolla M) portOrder).contract Signature.disequality

def delta : Signature K 2 := fun x=>if x 0=false ∧ x 1=true then 1 else 0

theorem contraction (M : Signature K 4) (t : Fin 2 → Bool) :
    (network M).denote t=M ![false,t 1,true,t 0]+M ![true,t 1,false,t 0] := by
  rw [network,Network.denote_contract,Chain.reindex_denote,Network.denote_corolla,
    Signature.contract_disequality]
  have hword (a b : Bool) :
      (fun i : Fin 4 => (Fin.cons a (Fin.cons b t) : Fin 4 → Bool) (portOrder i))=![a,t 1,b,t 0] := by
    funext i
    fin_cases i <;> rfl
  simp only [Tensor.reindex_apply,hword]

/-- Exact all-four coefficient identity. The nonzero scalar is the ORIGINAL
d=M(0110), with no rescaling of either corner or substitution of a square. -/
theorem denote (M : Signature K 4) (hM : EvenSupport M) (hs : SparseCase M) :
    (network M).denote=(entries M).d • delta := by
  funext t
  rw [contraction]
  rcases hs with ⟨hb,hy,hw,_hc,_hd,_hz⟩
  have hm := table_entries M hM
  rw [←hm]
  cases h0 : t 0 <;> cases h1 : t 1 <;>
    simp [table,delta,h0,h1,Pi.smul_apply,smul_eq_mul,hb,hy,hw] <;> rfl

theorem scale_nonzero (M : Signature K 4) (hs : SparseCase M) : (entries M).d≠0 := hs.2.2.2.2.1

def labels (M : Signature K 4) : Labelling (network M).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity _ := rfl
  edge _ := 0

abbrev template (M : Signature K 4) := (labels M).template

theorem valid (M : Signature K 4) : (template M).WellFormed 1 1 (fun _=>4) := (labels M).wellFormed

theorem records (M : Signature K 4) :
    (template M).boundary=2 ∧
      (template M).vertices=[(0,[.inr (0,false),.inl 1,.inr (0,true),.inl 0])] ∧
      (template M).edges=[0] := by
  constructor
  · rfl
  constructor <;> rfl

theorem template_actual (M : Signature K 4) :
    ((template M).network (valid M) (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
      (network M).denote := by
  apply Labelling.denote_template_of_labels (labels M) _ _ (network M).vertex (network M).edge
  · intro v x
    rfl
  · intro e a b
    fin_cases e
    rfl

theorem template_denote (M : Signature K 4) (hM : EvenSupport M) (hs : SparseCase M) :
    ((template M).network (valid M) (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
      (entries M).d • delta := by
  rw [template_actual]
  exact denote M hM hs

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseDirectPin
