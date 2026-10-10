import Holant.Proofs.Dichotomy.Closure.Singular.GlobalCloseCompletionSingularNAND
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryXAdjoin
import Holant.Complexity.BinaryInterpolation.Chains.Network

/-! Actual ordinary h-Z-h network. The diagonal Z is constructed by the
literal Eq4 vertex and two copies of the isotropic full unary; its nonzero
scalar is preserved by the existing literal-X adjoin compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularXGraph
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution Holant.LocalDrafts.MainChain
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex tensor_denote reindex_denote)
end C
namespace N
export GlobalCloseCompletionSingularNAND (traceless unary)
end N
namespace X
export GlobalCloseCompletionOrdinaryXAdjoin (Output)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K]

def order : Equiv.Perm (Fin 10) where
  toFun := ![8,0,2,9,1,3,5,7,4,6]
  invFun := ![1,4,2,5,8,6,9,7,0,3]
  left_inv := by decide
  right_inv := by decide

def tensor (h : Signature K 2) (u : Signature K 1) : Network K 10 :=
  C.tensor (C.tensor (Network.corolla h) (Network.corolla h))
    (C.tensor (Network.corolla Holant.EightVertex.ProductAnchor.equalityFour)
      (C.tensor (Network.corolla u) (Network.corolla u)))

def graph (h : Signature K 2) (u : Signature K 1) : Network K 2 :=
  ((((C.reindex (tensor h u) order).contract Signature.equality).contract
    Signature.equality).contract Signature.equality).contract Signature.equality

theorem wired_value (h : Signature K 2) (u : Signature K 1) (z : Fin 10→Bool) :
    (tensor h u).denote (fun i=>z (order i))=
      (h ![z 8,z 0]*h ![z 2,z 9])*
        (Holant.EightVertex.ProductAnchor.equalityFour ![z 1,z 3,z 5,z 7]*u ![z 4]*u ![z 6]) := by
  simp only [tensor,C.tensor_denote,Network.denote_corolla,
    Signature.tensor_apply]
  have hh0 : (fun i : Fin 2=>z (order (Fin.castAdd 6 (Fin.castAdd 2 i))))=![z 8,z 0] := by
    funext i; fin_cases i <;> rfl
  have hh1 : (fun i : Fin 2=>z (order (Fin.castAdd 6 (Fin.natAdd 2 i))))=![z 2,z 9] := by
    funext i; fin_cases i <;> rfl
  have he : (fun i : Fin 4=>z (order (Fin.natAdd 4 (Fin.castAdd 2 i))))=![z 1,z 3,z 5,z 7] := by
    funext i; fin_cases i <;> rfl
  have hu0 : (fun i : Fin 1=>z (order (Fin.natAdd 4 (Fin.natAdd 4 (Fin.castAdd 1 i)))))=![z 4] := by
    funext i; fin_cases i; rfl
  have hu1 : (fun i : Fin 1=>z (order (Fin.natAdd 4 (Fin.natAdd 4 (Fin.natAdd 1 i)))))=![z 6] := by
    funext i; fin_cases i; rfl
  rw [hh0,hh1,he,hu0,hu1]
  ring

theorem graph_value (x y u v : K) (z : Fin 2→Bool) :
    (graph (N.traceless x y) (N.unary u v)).denote z=
      N.traceless x y ![z 0,false]*N.traceless x y ![false,z 1]*u^2+
      N.traceless x y ![z 0,true]*N.traceless x y ![true,z 1]*v^2 := by
  have hz : z=![z 0,z 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  cases h0 : z 0 <;> cases h1 : z 1
  all_goals simp only [graph,Network.denote_contract,C.reindex_denote,Signature.contract_equality]
  all_goals simp only [Tensor.reindex_apply,wired_value]
  all_goals simp only [show ∀(n : ℕ)(a : Bool)(f : Fin n→Bool), Fin.cons a f=Matrix.vecCons a f from
    fun _ _ _=>rfl]
  all_goals norm_num [N.traceless,N.unary,Holant.EightVertex.ProductAnchor.equalityFour,
    Fin.forall_fin_succ]; ring

theorem graph_X (x y u v : K) (square : v^2= -u^2) (same : x^2=y^2) :
    (graph (N.traceless x y) (N.unary u v)).denote=
      fun z=>(u^2*(2*x*y))*Signature.disequality (z 0) (z 1) := by
  funext z
  rw [graph_value]
  cases h0 : z 0 <;> cases h1 : z 1 <;>
    simp [N.traceless,Signature.disequality,square] <;>
    ring_nf <;> simp [same] <;> ring

variable {s : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (b i.val)) (hj e uj : Fin s)
variable (x y u v : K)
variable (hh : (⟨b hj.val,H hj⟩ : AnySignature K)=⟨2,N.traceless x y⟩)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (hu : (⟨b uj.val,H uj⟩ : AnySignature K)=⟨1,N.unary u v⟩)

include hh he hu in
theorem vertices : ∀i,(⟨(graph (N.traceless x y) (N.unary u v)).shape.arity i,
    (graph (N.traceless x y) (N.unary u v)).vertex i⟩ : AnySignature K)∈
      UniversalPairReduction.FiniteFamily.family H := by
  intro i
  change Fin 5 at i
  fin_cases i
  · exact ⟨hj,hh⟩
  · exact ⟨hj,hh⟩
  · exact ⟨e,he⟩
  · exact ⟨uj,hu⟩
  · exact ⟨uj,hu⟩

theorem ordinary : ∀e,(graph (N.traceless x y) (N.unary u v)).edge e=Signature.equality := by
  intro i
  change Fin 4 at i
  fin_cases i <;> rfl

def labels := UniversalPairReduction.FiniteFamily.labelling H
  (graph (N.traceless x y) (N.unary u v)) (vertices H hj e uj x y u v hh he hu)

variable [Algebra ℚ K] [CharZero K]
variable (square : v^2= -u^2) (same : x^2=y^2) (nx : x≠0) (ny : y≠0) (nu : u≠0)

/-- This is the existing executable scalar-X adjoin input, with the actual
five-vertex graph and table labels, not a semantic gate supplier. -/
def output : X.Output H where
  network := graph (N.traceless x y) (N.unary u v)
  labels := labels H hj e uj x y u v hh he hu
  exact := fun i=>(vertices H hj e uj x y u v hh he hu i).choose_spec
  ordinary := ordinary x y u v
  scalar := u^2*(2*x*y)
  nonzero := mul_ne_zero (pow_ne_zero _ nu) (mul_ne_zero (mul_ne_zero (by norm_num) nx) ny)
  denote := graph_X x y u v square same

/-- The zero-diagonal branch uses the literal original binary corolla. -/
def directOutput (hzero : x=0) (nonzero : y≠0) : X.Output H where
  network := Network.corolla (N.traceless x y)
  labels := {vertex := fun _=>hj,vertex_arity := fun _=>congrArg Sigma.fst hh,edge := Fin.elim0}
  exact := fun _=>hh
  ordinary := by intro i; exact Fin.elim0 i
  scalar := y
  nonzero := nonzero
  denote := by
    rw [Network.denote_corolla,hzero]
    funext z
    cases h0 : z 0 <;> cases h1 : z 1 <;>
      simp [N.traceless,Signature.disequality,h0,h1]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularXGraph
end
