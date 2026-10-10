import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryNoInteractionCaps
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin
import Holant.Proofs.Hardness.GeneralOddNonisotropicFrame

/-! Saved factor trees belong to actual smaller zero-cap graphs. A single
explicit dummy unary reconstructs the all-original-ports cap used by the
UPF coefficient lemmas. No prime leaf is extracted from a fictitious graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroCapTrees
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (cap)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}
variable (H : (j : Fin r)→Signature K (a j.val))
variable (U : NoXOrdinaryGraphAdjoin.Output H 1) (N : NoXOrdinaryGraphAdjoin.Output H (n+1))
variable (scalar : K) (nonzeroScalar : scalar≠0)
variable (pin0 : U.network.denote (fun _=>false)=scalar)
variable (pin1 : U.network.denote (fun _=>true)=0)

def permutation (i : Fin (n+1)) : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
def graph (i : Fin (n+1)) : Network K n := capHead U.network (reboundary N.network (permutation i))

include pin0 pin1 in
theorem value (i : Fin (n+1)) (x : Fin n→Bool) :
    (graph H U N i).denote x=scalar*N.network.denote (fun j=>(Fin.cons false x : Fin (n+1)→Bool) (permutation i j)) := by
  rw [graph,capHead_denote,pin0,pin1,reboundary_denote]
  simp

def labels (i : Fin (n+1)) : Labelling (graph H U N i).shape r 1 a :=
  let hf:=capHead_uses (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K)) U.network
    (reboundary N.network (permutation i)) (fun v=>⟨U.labels.vertex v,U.exact v⟩)
    (fun v=>⟨N.labels.vertex v,N.exact v⟩)
  {vertex v:=Classical.choose (hf v)
   vertex_arity v:=congrArg Sigma.fst (Classical.choose_spec (hf v))
   edge _:=0}
theorem exact (i : Fin (n+1)) : LabelledNetwork.Exact H (graph H U N i) (labels H U N i) := by
  intro v
  exact Classical.choose_spec (capHead_uses (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K)) U.network
    (reboundary N.network (permutation i)) (fun v=>⟨U.labels.vertex v,U.exact v⟩)
    (fun v=>⟨N.labels.vertex v,N.exact v⟩) v)
theorem ordinary (i : Fin (n+1)) : Ordinary (graph H U N i) :=
  capHead_ordinary U.network (reboundary N.network (permutation i)) U.ordinary N.ordinary
def output (i : Fin (n+1)) : NoXOrdinaryGraphAdjoin.Output H n :=
  ⟨graph H U N i,labels H U N i,exact H U N i,ordinary H U N i⟩

variable (origin : N.network.denote (fun _=>false)≠0)
include nonzeroScalar pin0 pin1 origin in
theorem nonzero (i : Fin (n+1)) : (graph H U N i).denote≠0 := by
  intro zero
  have h:=congrFun zero (fun _=>false)
  rw [value H U N scalar pin0 pin1 i] at h
  have word : (fun j=>(Fin.cons false (fun _ : Fin n=>false) : Fin (n+1)→Bool) (permutation i j))=(fun _=>false) := by
    funext j
    generalize permutation i j=k
    exact Fin.cases rfl (fun _=>rfl) k
  rw [word] at h
  exact mul_ne_zero nonzeroScalar origin h

def tree (i : Fin (n+1)) : FactorTree (⟨n,(graph H U N i).denote⟩ : AnySignature K) :=
  Classical.choice (exists_factorTree _ (nonzero H U N scalar nonzeroScalar pin0 pin1 origin i))

def headPorts (n : ℕ) : (Fin 1 ⊕ Fin n) ≃ Fin (n+1) where
  toFun
    | .inl _=>0
    | .inr j=>j.succ
  invFun:=Fin.cases (.inl 0) (fun j=>.inr j)
  left_inv p:=by
    cases p with
    | inl j=>have h : j=0:=Fin.eq_zero j;subst j;rfl
    | inr j=>rfl
  right_inv j:=Fin.cases rfl (fun _=>rfl) j

theorem unary_prime : Prime (⟨1,fun _=>1⟩ : AnySignature K) := by
  refine ⟨?_,?_⟩
  · intro zero
    have h:=congrFun zero (fun _=>false)
    exact one_ne_zero h
  · rintro ⟨a,b,⟨s⟩⟩
    have h:=s.arity
    have ha:=s.left_pos
    have hb:=s.right_pos
    change a.1+b.1=1 at h
    omega

variable (positive : 0<n)
include pin0 pin1 in
def split (i : Fin (n+1)) : ProperSplit
    (⟨n+1,P.cap i N.network.denote⟩ : AnySignature K)
    ⟨1,fun _=>1⟩ ⟨n,(graph H U N i).denote⟩ where
  left_pos:=by change 0<1;decide
  right_pos:=positive
  ports:=(headPorts n).trans (permutation i)
  scale:=Units.mk0 scalar⁻¹ (inv_ne_zero nonzeroScalar)
  equation:=by
    funext x
    dsimp only
    rw [value H U N scalar pin0 pin1 i]
    have word : (fun j=>(Fin.cons false (fun k=>x (permutation i k.succ)) : Fin (n+1)→Bool) (permutation i j))=
        Function.update x i false := by
      funext j
      obtain ⟨k,rfl⟩:=(permutation i).surjective j
      refine Fin.cases ?_ (fun k=>?_) k
      · simp [permutation]
      · have ne : permutation i k.succ≠i := by
          rw [show i=permutation i 0 by simp [permutation]]
          exact (permutation i).injective.ne (Fin.succ_ne_zero k)
        rw [Function.update_of_ne ne]
        simp [permutation]
    change P.cap i N.network.denote x=scalar⁻¹*(1*(scalar*N.network.denote
      (fun j=>(Fin.cons false (fun k=>x (permutation i k.succ)) : Fin (n+1)→Bool) (permutation i j))))
    rw [word,one_mul,←mul_assoc,inv_mul_cancel₀ nonzeroScalar,one_mul]
    rfl

def liftedTree (i : Fin (n+1)) : FactorTree (⟨n+1,P.cap i N.network.denote⟩ : AnySignature K) :=
  .split (split H U N scalar nonzeroScalar pin0 pin1 positive i) (.leaf _ unary_prime)
    (tree H U N scalar nonzeroScalar pin0 pin1 origin i)

theorem lifted_small (small : ∀i,∀g∈(tree H U N scalar nonzeroScalar pin0 pin1 origin i).leaves,g.1≤2) :
    ∀i,∀g∈(liftedTree H U N scalar nonzeroScalar pin0 pin1 origin positive i).leaves,g.1≤2 := by
  intro i g hg
  rcases Multiset.mem_add.mp hg with unary|other
  · have h : g=(⟨1,fun _=>1⟩ : AnySignature K) := by
      simpa only [FactorTree.leaves,Multiset.mem_singleton] using unary
    rw [h]
    change 1≤2
    decide
  · exact small i g other


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroCapTrees
end
