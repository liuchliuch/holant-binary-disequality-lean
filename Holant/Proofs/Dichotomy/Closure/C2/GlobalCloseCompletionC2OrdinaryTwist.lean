import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryAttach

/-! A generic ordinary-Z construction for complementary-even quaternaries.
All Z gates are actual binary vertices and every edge is literal equality.
The two-copy twist produces a symmetric pair, whose determinant gives an
actual four-copy Eq4 graph with its exact nonzero scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryTwist
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.EightVertex.ProductAnchor
namespace A
export GlobalCloseCompletionKleinOrdinaryAttach (attach attach_denote labels exact ordinary)
end A
namespace P
export GlobalCloseCompletionKleinOrdinaryPair
  (pair symmetric zSignature series seriesLabels series_exact series_ordinary network denote labels exact ordinary)
end P
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z normal sparse)
end T
namespace C
export BinaryInterpolation.Chains (tensor tensor_denote reindex reindex_denote)
end C
namespace O
export Holant.Certificates.EqualityQuaternary.Klein.Orbit (site)
end O
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex seriesOrder)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

def zKernel (z : K) : Kernel K := fun a b => z*T.Z a b

theorem attach_Z (N : Network K 4) (i : Fin 4) (z : K) :
    (A.attach N i (zKernel z)).denote = fun x => z*(if x i then -1 else 1)*N.denote x := by
  rw [A.attach_denote]
  funext x
  have hu : Function.update x i (x i)=x := Function.update_eq_self i x
  cases h : x i
  all_goals
    rw [h] at hu
    simp [O.site,zKernel,T.Z,h,hu]

theorem series_value (L R : Network K 4) (x : Fin 4→Bool) :
    (P.series L R).denote x =
      (L.denote ![x 0,x 1,false,false]*R.denote ![false,false,x 2,x 3]+
       L.denote ![x 0,x 1,true,false]*R.denote ![false,true,x 2,x 3])+
      (L.denote ![x 0,x 1,false,true]*R.denote ![true,false,x 2,x 3]+
       L.denote ![x 0,x 1,true,true]*R.denote ![true,true,x 2,x 3]) := by
  rw [P.series,Network.denote_contract_equality,Network.denote_contract_equality,
    Network.denote_contract_equality,C.reindex_denote,C.tensor_denote]
  have eval (u v w z : Bool) :
      Tensor.reindex M.seriesOrder (L.denote.tensor R.denote)
        (Fin.cons u (Fin.cons v (Fin.cons w (Fin.cons z x)))) =
      L.denote ![x 0,x 1,u,w]*R.denote ![z,v,x 2,x 3] := by
    simp only [Tensor.reindex_apply,Signature.tensor_apply]
    congr 1 <;> apply congrArg _ <;> funext i <;> fin_cases i <;> rfl
  simp only [eval]

def twist (N : Network K 4) (z : K) : Network K 4 :=
  P.series (A.attach N 2 (zKernel z)) (C.reindex N (Equiv.swap 0 1))

theorem twist_normal (N : Network K 4) (z a b c d : K)
    (form : N.denote=T.normal a b c d) :
    (twist N z).denote=z • T.sparse (a^2-b^2) (c^2-d^2) := by
  funext x
  rw [twist,series_value,attach_Z,C.reindex_denote,form]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,T.normal,T.sparse,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> ring

def pairGraph (N : Network K 4) (z : K) : Network K 4 :=
  C.reindex (A.attach (twist N z) 0 (zKernel z)) (Equiv.swap 1 2)

theorem pairGraph_normal (N : Network K 4) (z a b c d : K)
    (form : N.denote=T.normal a b c d) :
    (pairGraph N z).denote=P.pair (M.binary (P.symmetric (z^2*(a^2-b^2)) (z^2*(c^2-d^2)))) := by
  rw [pairGraph,C.reindex_denote,attach_Z,twist_normal N z a b c d form]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,Equiv.swap_apply_def,T.sparse,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      P.pair,M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3] <;> ring

def eq4Graph (N : Network K 4) (z : K) : Network K 4 := P.network (pairGraph N z) z

theorem eq4Graph_denote (N : Network K 4) (z a b c d : K)
    (form : N.denote=T.normal a b c d) :
    (eq4Graph N z).denote=(z^6*((a^2-b^2)^2-(c^2-d^2)^2)) • equalityFour := by
  rw [eq4Graph,P.denote _ z _ _ (pairGraph_normal N z a b c d form)]
  congr 1
  ring

section Labels
variable {s : ℕ} {b : ℕ→ℕ} (H : (i : Fin s)→Signature K (b i.val))
variable (N : Network K 4) (L : Labelling N.shape s 1 b) (j : Fin s) (z : K)
variable (literalZ : (⟨b j.val,H j⟩ : AnySignature K)=⟨2,P.zSignature z⟩)

def twistLabels : Labelling (twist N z).shape s 1 b :=
  P.seriesLabels (A.attach N 2 (zKernel z)) (A.labels H N L j (zKernel z) literalZ 2)
    (C.reindex N (Equiv.swap 0 1)) (LabelledNetwork.reindex N L (Equiv.swap 0 1))

theorem twist_exact (input : LabelledNetwork.Exact H N L) :
    LabelledNetwork.Exact H (twist N z) (twistLabels H N L j z literalZ) :=
  P.series_exact H _ _ _ _ (A.exact H N L j (zKernel z) literalZ 2 input) input

def pairLabels : Labelling (pairGraph N z).shape s 1 b :=
  LabelledNetwork.reindex _
    (A.labels H (twist N z) (twistLabels H N L j z literalZ) j (zKernel z) literalZ 0)
    (Equiv.swap 1 2)

theorem pair_exact (input : LabelledNetwork.Exact H N L) :
    LabelledNetwork.Exact H (pairGraph N z) (pairLabels H N L j z literalZ) :=
  A.exact H _ _ j (zKernel z) literalZ 0 (twist_exact H N L j z literalZ input)

def eq4Labels : Labelling (eq4Graph N z).shape s 1 b :=
  P.labels H (pairGraph N z) (pairLabels H N L j z literalZ) j z literalZ

theorem eq4_exact (input : LabelledNetwork.Exact H N L) :
    LabelledNetwork.Exact H (eq4Graph N z) (eq4Labels H N L j z literalZ) :=
  P.exact H _ _ j z literalZ (pair_exact H N L j z literalZ input)
end Labels

theorem eq4_ordinary (N : Network K 4) (z : K) (input : ∀e,N.edge e=Signature.equality) :
    ∀e,(eq4Graph N z).edge e=Signature.equality :=
  P.ordinary _ z (A.ordinary _ 0 (zKernel z)
    (P.series_ordinary _ _ (A.ordinary N 2 (zKernel z) input) input))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryTwist
end
