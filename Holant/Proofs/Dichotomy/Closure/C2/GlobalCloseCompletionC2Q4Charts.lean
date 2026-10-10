import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4KTensor
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSixSquare

/-! Every checked q4 subspace has an actual ordinary chart using only a port
permutation and zero or one retained Z vertex. Both pure parity spaces and
all six mixed-parity spaces retain their exact original coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Charts
open Holant Holant.Tractable
open Holant.Pauli.ExoticKlein.SixPort
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped QuadraticAlgebra
namespace U
export GlobalCloseCompletionC2Q4Union (Holds Accepted targetRows)
end U
namespace I
export GlobalCloseCompletionC2SparseInteger (Row toIRow toIRows value)
end I
namespace M
export GlobalCloseCompletionC2Q4KTensor (entries sourceK_tensor)
end M
namespace C
export GlobalCloseCompletionC2Q4UnionCurrent (tensor)
end C
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option Elab.async false

def algebraicEvaluate (r : I.Row) (v : Fin 8→AlgebraicComplex) : AlgebraicComplex :=
  ∑i,(I.value r i.val : AlgebraicComplex)*v i

theorem evaluate_cast (r : I.Row) (v : Fin 8→AlgebraicComplex) :
    LinearCertificate.evaluate (IntegerCertificate.mapRow (I.toIRow r)) (fun i=>(v i:ℂ))=
      (algebraicEvaluate r v:ℂ) := by
  simp [LinearCertificate.evaluate,IntegerCertificate.mapRow,I.toIRow,algebraicEvaluate]

theorem algebraic_holds (r : List I.Row) (v : Fin 8→AlgebraicComplex)
    (h : U.Holds r (fun i=>(v i:ℂ))) : ∀row∈r,algebraicEvaluate row v=0 := by
  intro row member
  apply Subtype.ext
  change (algebraicEvaluate row v:ℂ)=0
  rw [←evaluate_cast]
  exact h _ (List.mem_map.mpr ⟨I.toIRow row,List.mem_map.mpr ⟨row,member,rfl⟩,rfl⟩)

def permutation (j : Fin 8) : Equiv.Perm (Fin 4) where
  toFun := (![![0,1,2,3],![0,1,2,3],![0,3,2,1],![0,3,2,1],![0,2,1,3],![0,1,2,3],![0,2,1,3],![0,1,2,3]] : Fin 8→Fin 4→Fin 4) j
  invFun := (![![0,1,2,3],![0,1,2,3],![0,3,2,1],![0,3,2,1],![0,2,1,3],![0,1,2,3],![0,2,1,3],![0,1,2,3]] : Fin 8→Fin 4→Fin 4) j
  left_inv := by fin_cases j <;> decide
  right_inv := by fin_cases j <;> decide

def flip : Fin 8→Bool := ![false,true,true,false,true,true,false,false]
def phase (b : Bool) (f : Signature AlgebraicComplex 4) : Signature AlgebraicComplex 4 :=
  fun x=>(if b && x 0 then -1 else 1)*f x
def chart (j : Fin 8) (v : Fin 8→AlgebraicComplex) : Signature AlgebraicComplex 4 :=
  phase (flip j) (Tensor.reindex (permutation j) (sourceKBasis.action (C.tensor v)))
def Shape (f : Signature AlgebraicComplex 4) : Prop :=
  (∃a b c d,f=T.normal a b c d) ∨ ∃b c d,f=S.signed b c d

theorem shape0 (v : Fin 8→AlgebraicComplex) (h : U.Holds (U.targetRows 0) (fun i=>(v i:ℂ))) : Shape (chart 0 v) := by
  have hh := algebraic_holds (U.targetRows 0) v h
  have e0 := hh [(1,(1))] (by simp [U.targetRows])
  have e1 := hh [(2,(1))] (by simp [U.targetRows])
  have e2 := hh [(4,(1))] (by simp [U.targetRows])
  have e3 := hh [(7,(1))] (by simp [U.targetRows])
  norm_num [algebraicEvaluate,I.value,Fin.sum_univ_succ] at e0 e1 e2 e3
  left
  refine ⟨chart 0 v ![false,false,false,false],chart 0 v ![false,false,true,true],chart 0 v ![false,true,false,true],chart 0 v ![false,true,true,false],?_⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (-1)*e1 + (-1)*e2 + (1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (-1)*e1 + (1)*e2 + (-1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (1)*e1 + (-1)*e2 + (-1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (-1)*e0 + (-1)*e1 + (-1)*e2 + (-1)*e3

theorem shape1 (v : Fin 8→AlgebraicComplex) (h : U.Holds (U.targetRows 1) (fun i=>(v i:ℂ))) : Shape (chart 1 v) := by
  have hh := algebraic_holds (U.targetRows 1) v h
  have e0 := hh [(0,(1))] (by simp [U.targetRows])
  have e1 := hh [(3,(1))] (by simp [U.targetRows])
  have e2 := hh [(5,(1))] (by simp [U.targetRows])
  have e3 := hh [(6,(1))] (by simp [U.targetRows])
  norm_num [algebraicEvaluate,I.value,Fin.sum_univ_succ] at e0 e1 e2 e3
  left
  refine ⟨chart 1 v ![false,false,false,false],chart 1 v ![false,false,true,true],chart 1 v ![false,true,false,true],chart 1 v ![false,true,true,false],?_⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (-1)*e1 + (-1)*e2 + (1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (-1)*e1 + (1)*e2 + (-1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (1)*e1 + (-1)*e2 + (-1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (-1)*e0 + (-1)*e1 + (-1)*e2 + (-1)*e3

theorem shape2 (v : Fin 8→AlgebraicComplex) (h : U.Holds (U.targetRows 2) (fun i=>(v i:ℂ))) : Shape (chart 2 v) := by
  have hh := algebraic_holds (U.targetRows 2) v h
  have e0 := hh [(0,(1)),(6,(-1))] (by simp [U.targetRows])
  have e1 := hh [(1,(1)),(7,(1))] (by simp [U.targetRows])
  have e2 := hh [(2,(1)),(4,(1))] (by simp [U.targetRows])
  have e3 := hh [(3,(1)),(6,(1))] (by simp [U.targetRows])
  have e4 := hh [(5,(1)),(6,(1))] (by simp [U.targetRows])
  norm_num [algebraicEvaluate,I.value,Fin.sum_univ_succ] at e0 e1 e2 e3 e4
  right
  refine ⟨chart 2 v ![false,false,true,true],chart 2 v ![false,true,false,true],chart 2 v ![false,true,true,false],?_⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((1/2))*e0 + ((1/2))*e1 + ((1/2))*e2 + ((1/2))*e3 + ((1/2))*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (1)*e3 + (-1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (-1)*e3 + (1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (-1)*e1 + (1)*e2
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((-1/2))*e0 + ((1/2))*e1 + ((1/2))*e2 + ((-1/2))*e3 + ((-1/2))*e4

theorem shape3 (v : Fin 8→AlgebraicComplex) (h : U.Holds (U.targetRows 3) (fun i=>(v i:ℂ))) : Shape (chart 3 v) := by
  have hh := algebraic_holds (U.targetRows 3) v h
  have e0 := hh [(0,(1)),(6,(1))] (by simp [U.targetRows])
  have e1 := hh [(1,(1)),(7,(-1))] (by simp [U.targetRows])
  have e2 := hh [(2,(1)),(7,(1))] (by simp [U.targetRows])
  have e3 := hh [(3,(1)),(5,(1))] (by simp [U.targetRows])
  have e4 := hh [(4,(1)),(7,(1))] (by simp [U.targetRows])
  norm_num [algebraicEvaluate,I.value,Fin.sum_univ_succ] at e0 e1 e2 e3 e4
  right
  refine ⟨chart 3 v ![false,false,true,true],chart 3 v ![false,true,false,true],chart 3 v ![false,true,true,false],?_⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((1/2))*e0 + ((1/2))*e1 + ((1/2))*e2 + ((1/2))*e3 + ((1/2))*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e1 + (1)*e2 + (-1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e1 + (-1)*e2 + (1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (-1)*e0 + (1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((1/2))*e0 + ((-1/2))*e1 + ((-1/2))*e2 + ((1/2))*e3 + ((-1/2))*e4

theorem shape4 (v : Fin 8→AlgebraicComplex) (h : U.Holds (U.targetRows 4) (fun i=>(v i:ℂ))) : Shape (chart 4 v) := by
  have hh := algebraic_holds (U.targetRows 4) v h
  have e0 := hh [(0,(1)),(6,(1))] (by simp [U.targetRows])
  have e1 := hh [(1,(1)),(4,(1))] (by simp [U.targetRows])
  have e2 := hh [(2,(1)),(7,(1))] (by simp [U.targetRows])
  have e3 := hh [(3,(1)),(6,(-1))] (by simp [U.targetRows])
  have e4 := hh [(5,(1)),(6,(1))] (by simp [U.targetRows])
  norm_num [algebraicEvaluate,I.value,Fin.sum_univ_succ] at e0 e1 e2 e3 e4
  right
  refine ⟨chart 4 v ![false,false,true,true],chart 4 v ![false,true,false,true],chart 4 v ![false,true,true,false],?_⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((1/2))*e0 + ((1/2))*e1 + ((1/2))*e2 + ((1/2))*e3 + ((1/2))*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (-1)*e3 + (-1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (1)*e3 + (-1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (-1)*e1 + (1)*e2
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((-1/2))*e0 + ((1/2))*e1 + ((1/2))*e2 + ((-1/2))*e3 + ((-1/2))*e4

theorem shape5 (v : Fin 8→AlgebraicComplex) (h : U.Holds (U.targetRows 5) (fun i=>(v i:ℂ))) : Shape (chart 5 v) := by
  have hh := algebraic_holds (U.targetRows 5) v h
  have e0 := hh [(0,(1)),(6,(1))] (by simp [U.targetRows])
  have e1 := hh [(1,(1)),(2,(1))] (by simp [U.targetRows])
  have e2 := hh [(3,(1)),(6,(1))] (by simp [U.targetRows])
  have e3 := hh [(4,(1)),(7,(1))] (by simp [U.targetRows])
  have e4 := hh [(5,(1)),(6,(-1))] (by simp [U.targetRows])
  norm_num [algebraicEvaluate,I.value,Fin.sum_univ_succ] at e0 e1 e2 e3 e4
  right
  refine ⟨chart 5 v ![false,false,true,true],chart 5 v ![false,true,false,true],chart 5 v ![false,true,true,false],?_⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((1/2))*e0 + ((1/2))*e1 + ((1/2))*e2 + ((1/2))*e3 + ((1/2))*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (-1)*e2 + (-1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e0 + (-1)*e2 + (1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (-1)*e1 + (1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((-1/2))*e0 + ((1/2))*e1 + ((-1/2))*e2 + ((1/2))*e3 + ((-1/2))*e4

theorem shape6 (v : Fin 8→AlgebraicComplex) (h : U.Holds (U.targetRows 6) (fun i=>(v i:ℂ))) : Shape (chart 6 v) := by
  have hh := algebraic_holds (U.targetRows 6) v h
  have e0 := hh [(0,(1)),(5,(1))] (by simp [U.targetRows])
  have e1 := hh [(1,(1)),(7,(1))] (by simp [U.targetRows])
  have e2 := hh [(2,(1)),(7,(-1))] (by simp [U.targetRows])
  have e3 := hh [(3,(1)),(6,(1))] (by simp [U.targetRows])
  have e4 := hh [(4,(1)),(7,(1))] (by simp [U.targetRows])
  norm_num [algebraicEvaluate,I.value,Fin.sum_univ_succ] at e0 e1 e2 e3 e4
  right
  refine ⟨chart 6 v ![false,false,true,true],chart 6 v ![false,true,false,true],chart 6 v ![false,true,true,false],?_⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((1/2))*e0 + ((1/2))*e1 + ((1/2))*e2 + ((1/2))*e3 + ((1/2))*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e1 + (-1)*e2 + (-1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e1 + (1)*e2 + (-1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (-1)*e0 + (1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((1/2))*e0 + ((-1/2))*e1 + ((-1/2))*e2 + ((1/2))*e3 + ((-1/2))*e4

theorem shape7 (v : Fin 8→AlgebraicComplex) (h : U.Holds (U.targetRows 7) (fun i=>(v i:ℂ))) : Shape (chart 7 v) := by
  have hh := algebraic_holds (U.targetRows 7) v h
  have e0 := hh [(0,(1)),(3,(1))] (by simp [U.targetRows])
  have e1 := hh [(1,(1)),(7,(1))] (by simp [U.targetRows])
  have e2 := hh [(2,(1)),(7,(1))] (by simp [U.targetRows])
  have e3 := hh [(4,(1)),(7,(-1))] (by simp [U.targetRows])
  have e4 := hh [(5,(1)),(6,(1))] (by simp [U.targetRows])
  norm_num [algebraicEvaluate,I.value,Fin.sum_univ_succ] at e0 e1 e2 e3 e4
  right
  refine ⟨chart 7 v ![false,false,true,true],chart 7 v ![false,true,false,true],chart 7 v ![false,true,true,false],?_⟩
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((1/2))*e0 + ((1/2))*e1 + ((1/2))*e2 + ((1/2))*e3 + ((1/2))*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e1 + (-1)*e2 + (-1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (1)*e1 + (-1)*e2 + (1)*e3
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination (-1)*e0 + (1)*e4
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> ring
  · simp only [chart,M.sourceK_tensor]
    <;> dsimp [phase,flip,permutation,M.entries,Tensor.reindex,T.normal,S.signed,table]
    <;> simp only [h0,h1,h2,h3]
    <;> (try dsimp)
    <;> linear_combination ((1/2))*e0 + ((-1/2))*e1 + ((-1/2))*e2 + ((-1/2))*e3 + ((1/2))*e4

theorem accepted_chart (v : Fin 8→AlgebraicComplex) (h : U.Accepted (fun i=>(v i:ℂ))) :
    ∃j : Fin 8,Shape (chart j v) := by
  obtain ⟨j,hj⟩ := h
  refine ⟨j,?_⟩
  fin_cases j
  · exact shape0 v hj
  · exact shape1 v hj
  · exact shape2 v hj
  · exact shape3 v hj
  · exact shape4 v hj
  · exact shape5 v hj
  · exact shape6 v hj
  · exact shape7 v hj

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Charts
end
