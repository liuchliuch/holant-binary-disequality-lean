import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinTwistedAlgebra
import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseEq4Flip

/-! An actual ordinary sparse-pair tensor and a retained scaled Z row produce
scalar Eq4 in two copies. Both Z insertions are real binary vertices, all
edges are ordinary I, and the output scalar is z²(a²-d²). -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryPair
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.EightVertex.ProductAnchor
namespace C
export BinaryInterpolation.Chains (tensor tensor_denote reindex reindex_denote)
end C
namespace M
export GeneralEOAffinePlaneChain (Mat binary table bitIndex seriesOrder)
end M
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

def pair (f : Signature K 2) : Signature K 4 := fun x=>
  if x 1=x 0 ∧ x 3=x 2 then f ![x 0,x 2] else 0

def symmetric (a d : K) : M.Mat (K:=K) := !![a,d;d,a]
def zMatrix : M.Mat (K:=K) := !![1,0;0,-1]
def zSignature (z : K) : Signature K 2 := fun x=>z*T.Z (x 0) (x 1)

def phase (N : Network K 4) (z : K) : Network K 4 :=
  (C.reindex (C.tensor N (Network.corolla (zSignature z)))
    (GlobalCloseCompletionSparseEq4Flip.order false)).contract Signature.equality

theorem phase_denote (N : Network K 4) (z : K) :
    (phase N z).denote=fun x=>z*(if x 1 then -1 else 1)*N.denote x := by
  funext x
  rw [phase,Network.denote_contract_equality,C.reindex_denote,C.tensor_denote,Network.denote_corolla]
  have eval (u v : Bool) :
      Tensor.reindex (GlobalCloseCompletionSparseEq4Flip.order false)
        (N.denote.tensor (zSignature z)) (Fin.cons u (Fin.cons v x))=
      N.denote ![x 0,u,x 2,x 3]*z*T.Z (x 1) v := by
    simp only [Tensor.reindex_apply,Signature.tensor_apply]
    have left : (fun i : Fin 4=>(Fin.cons u (Fin.cons v x) : Fin 6→Bool)
        ((GlobalCloseCompletionSparseEq4Flip.order false) (Fin.castAdd 2 i)))=![x 0,u,x 2,x 3] := by
      funext i
      fin_cases i <;> rfl
    have right : (fun i : Fin 2=>(Fin.cons u (Fin.cons v x) : Fin 6→Bool)
        ((GlobalCloseCompletionSparseEq4Flip.order false) (Fin.natAdd 4 i)))=![x 1,v] := by
      funext i
      fin_cases i <;> rfl
    rw [left,right]
    simp only [zSignature,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  rw [eval,eval]
  have eta : (![x 0,x 1,x 2,x 3] : Fin 4→Bool)=x := by funext i; fin_cases i <;> rfl
  have value := congrArg N.denote eta
  cases hx : x 1
  all_goals
    rw [hx] at value
    simp [T.Z,hx,value]
    ring

theorem phase_pair (N : Network K 4) (z : K) (A : M.Mat (K:=K))
    (form : N.denote=pair (M.binary A)) :
    (phase N z).denote=pair (M.binary ((z • zMatrix)*A)) := by
  rw [phase_denote,form]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [pair,M.binary,M.bitIndex,zMatrix,Matrix.mul_apply,Fin.sum_univ_two,h0,h1,h2,h3] <;> ring

def series (L R : Network K 4) : Network K 4 :=
  ((C.reindex (C.tensor L R) M.seriesOrder).contract Signature.equality).contract Signature.equality

theorem series_denote (L R : Network K 4) (A B : M.Mat (K:=K))
    (left : L.denote=pair (M.binary A)) (right : R.denote=pair (M.binary B)) :
    (series L R).denote=pair (M.binary (A*B)) := by
  funext x
  rw [series,Network.denote_contract_equality,Network.denote_contract_equality,
    Network.denote_contract_equality,C.reindex_denote,C.tensor_denote,left,right]
  change (pair (M.binary A) ![x 0,x 1,false,false]*pair (M.binary B) ![false,false,x 2,x 3]+
    pair (M.binary A) ![x 0,x 1,true,false]*pair (M.binary B) ![false,true,x 2,x 3])+
    (pair (M.binary A) ![x 0,x 1,false,true]*pair (M.binary B) ![true,false,x 2,x 3]+
    pair (M.binary A) ![x 0,x 1,true,true]*pair (M.binary B) ![true,true,x 2,x 3])=_
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [pair,M.binary,M.bitIndex,Matrix.mul_apply,Fin.sum_univ_two,h0,h1,h2,h3] <;> ring

def network (N : Network K 4) (z : K) : Network K 4 := phase (series N (phase N z)) z

theorem denote (N : Network K 4) (z a d : K) (form : N.denote=pair (M.binary (symmetric a d))) :
    (network N z).denote=(z^2*(a^2-d^2)) • equalityFour := by
  have inner := phase_pair N z (symmetric a d) form
  have middle := series_denote N (phase N z) (symmetric a d) _ form inner
  have outer := phase_pair (series N (phase N z)) z _ middle
  have matrix : (z • zMatrix)*(symmetric a d*((z • zMatrix)*symmetric a d))=
      (z^2*(a^2-d^2)) • (1 : M.Mat (K:=K)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetric,zMatrix,Matrix.mul_apply,Fin.sum_univ_two] <;> ring_nf <;> simp
  change (phase (series N (phase N z)) z).denote=_
  rw [outer,matrix]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [pair,M.binary,M.bitIndex,equalityFour,Fin.forall_fin_succ,h0,h1,h2,h3]

def pairOrder : Equiv.Perm (Fin 4) where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by decide
  right_inv := by decide

theorem normal_pair (a d : K) :
    Tensor.reindex pairOrder (T.normal a 0 0 d)=pair (M.binary (symmetric a d)) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,pairOrder,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      pair,M.binary,M.bitIndex,symmetric,h0,h1,h2,h3]

section Labels
variable {s : ℕ} {b : ℕ→ℕ} (H : (i : Fin s)→Signature K (b i.val))
variable (N : Network K 4) (L : Labelling N.shape s 1 b) (j : Fin s) (z : K)
variable (literalZ : (⟨b j.val,H j⟩ : AnySignature K)=⟨2,zSignature z⟩)

def zLabels : Labelling (Network.corolla (zSignature z)).shape s 1 b where
  vertex _ := j
  vertex_arity _ := congrArg Sigma.fst literalZ
  edge := Fin.elim0

def phaseLabels : Labelling (phase N z).shape s 1 b :=
  LabelledNetwork.contract _
    (LabelledNetwork.reindex _ (LabelledNetwork.tensor _ _ L (zLabels H j z literalZ))
      (GlobalCloseCompletionSparseEq4Flip.order false)) 0 Signature.equality

theorem phase_exact (exact : LabelledNetwork.Exact H N L) :
    LabelledNetwork.Exact H (phase N z) (phaseLabels H N L j z literalZ) :=
  LabelledNetwork.exact_tensor N (Network.corolla (zSignature z)) L (zLabels H j z literalZ)
    H exact (fun _=>literalZ)

def seriesLabels (R : Network K 4) (RL : Labelling R.shape s 1 b) :
    Labelling (series N R).shape s 1 b :=
  LabelledNetwork.contract _ (LabelledNetwork.contract _
    (LabelledNetwork.reindex _ (LabelledNetwork.tensor N R L RL) M.seriesOrder)
    0 Signature.equality) 0 Signature.equality

theorem series_exact (R : Network K 4) (RL : Labelling R.shape s 1 b)
    (left : LabelledNetwork.Exact H N L) (right : LabelledNetwork.Exact H R RL) :
    LabelledNetwork.Exact H (series N R) (seriesLabels N L R RL) :=
  LabelledNetwork.exact_tensor N R L RL H left right

def labels : Labelling (network N z).shape s 1 b :=
  phaseLabels H (series N (phase N z))
    (seriesLabels N L (phase N z) (phaseLabels H N L j z literalZ)) j z literalZ

theorem exact (input : LabelledNetwork.Exact H N L) :
    LabelledNetwork.Exact H (network N z) (labels H N L j z literalZ) :=
  phase_exact H _ _ j z literalZ
    (series_exact H N L _ _ input (phase_exact H N L j z literalZ input))
end Labels

theorem phase_ordinary (N : Network K 4) (z : K) (ordinary : ∀e,N.edge e=Signature.equality) :
    ∀e,(phase N z).edge e=Signature.equality := by
  intro e
  refine Fin.cases rfl (fun e=>?_) e
  change (Network.tensorFinite N (Network.corolla (zSignature z))).edge (finSumFinEquiv.symm e)=_
  cases finSumFinEquiv.symm e with
  | inl e => exact ordinary e
  | inr e => exact Fin.elim0 e

theorem series_ordinary (L R : Network K 4)
    (left : ∀e,L.edge e=Signature.equality) (right : ∀e,R.edge e=Signature.equality) :
    ∀e,(series L R).edge e=Signature.equality := by
  intro e
  refine Fin.cases rfl (fun e=>?_) e
  refine Fin.cases rfl (fun e=>?_) e
  change (Network.tensorFinite L R).edge (finSumFinEquiv.symm e)=_
  cases finSumFinEquiv.symm e with
  | inl e => exact left e
  | inr e => exact right e

theorem ordinary (N : Network K 4) (z : K) (input : ∀e,N.edge e=Signature.equality) :
    ∀e,(network N z).edge e=Signature.equality :=
  phase_ordinary _ z (series_ordinary N (phase N z) input (phase_ordinary N z input))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryPair
end
