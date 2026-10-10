import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryOrbit
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryPrime

/-! A genuine prime exotic Klein quaternary produces ordinary scalar Eq4
from its explicit orbit word in Hadamard coordinates. The determinant and
all orbit scalars are proved nonzero, including endpoint-zero inputs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryExoticEq4
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Certificates.EqualityQuaternary
namespace O
export GlobalCloseCompletionKleinOrdinaryOrbit (run scalar scalar_nonzero run_denote run_ordinary runLabels run_exact)
end O
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric network denote ordinary labels exact normal_pair pairOrder)
end P
namespace C
export BinaryInterpolation.Chains (reindex reindex_denote)
end C
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
export GlobalCloseCompletionKleinOrdinaryHTransport (H)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem plane_normal (a b : AlgebraicComplex) :
    Exotic.plane a b=T.normal (a-2*b) (a+2*b) (a+2*b) (a-2*b) := by
  funext x
  rw [Exotic.plane_table]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Holant.Marked.SupportAtlas.parity,T.normal,
      Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]

theorem H_plane (a b : AlgebraicComplex) :
    T.H.symm.action (Exotic.plane a b)=T.normal (a/2) 0 0 (-b) := by
  rw [plane_normal,GlobalCloseCompletionKleinBAlgebra.H_normal]
  congr 1 <;> ring

theorem pair_scale (c a d : AlgebraicComplex) :
    (fun x=>c*P.pair (M.binary (P.symmetric a d)) x)=P.pair (M.binary (P.symmetric (c*a) (c*d))) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [P.pair,M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3]

variable {F : SignatureFamily AlgebraicComplex} (reps : Klein.Representatives F .exotic)
variable (q : Signature AlgebraicComplex 4) (prime : TensorPrime q) (safe : Klein.PhysicalDeck reps q)

def index : Fin 24 := (Klein.source_exotic_representative reps q safe).choose
abbrev word := Klein.Orbit.paths (index reps q safe)
abbrev normalized := Klein.Orbit.actualRun reps (word reps q safe) q

theorem representative : Klein.Orbit.Representative (normalized reps q safe) :=
  (Klein.source_exotic_representative reps q safe).choose_spec

def left : AlgebraicComplex :=
  ((normalized reps q safe (fun _=>false)+normalized reps q safe ![false,false,true,true])/2)/2

def right : AlgebraicComplex :=
  -((normalized reps q safe ![false,false,true,true]-normalized reps q safe (fun _=>false))/4)

theorem normalized_pair :
    Tensor.reindex P.pairOrder (T.H.symm.action (normalized reps q safe))=
      P.pair (M.binary (P.symmetric (left reps q safe) (right reps q safe))) := by
  rw [Klein.Orbit.representative_plane (representative reps q safe),H_plane,P.normal_pair]
  rfl

def paired (N : Network AlgebraicComplex 4) : Network AlgebraicComplex 4 :=
  C.reindex (O.run reps (word reps q safe) N) P.pairOrder

theorem paired_denote (N : Network AlgebraicComplex 4)
    (form : N.denote=T.H.symm.action q) :
    (paired reps q safe N).denote=P.pair (M.binary (P.symmetric
      (O.scalar (word reps q safe)*left reps q safe)
      (O.scalar (word reps q safe)*right reps q safe))) := by
  rw [paired,C.reindex_denote,O.run_denote reps (word reps q safe) N q 1
    (by simpa only [one_mul] using form),mul_one]
  have h := normalized_pair reps q safe
  change (fun x=>O.scalar (word reps q safe)*Tensor.reindex P.pairOrder
    (T.H.symm.action (normalized reps q safe)) x)=_
  rw [h,pair_scale]

include prime in
theorem separated :
    (O.scalar (word reps q safe)*left reps q safe)^2≠
      (O.scalar (word reps q safe)*right reps q safe)^2 := by
  have hp := Klein.Orbit.actualRun_prime reps (word reps q safe) prime
  have ht : TensorPrime (T.H.symm.action (normalized reps q safe)) :=
    prime_coordinateAction hp (fun _=>T.H.inverse) (fun _=>T.H.matrix) (fun _=>T.H.matrix_inverse)
  have hr := C2.prime_reindex ht P.pairOrder
  rw [normalized_pair] at hr
  have hs := prime_smul hr (O.scalar (word reps q safe)) (O.scalar_nonzero (word reps q safe))
  change TensorPrime (fun x=>O.scalar (word reps q safe)*P.pair
    (M.binary (P.symmetric (left reps q safe) (right reps q safe))) x) at hs
  rw [pair_scale] at hs
  exact GlobalCloseCompletionKleinOrdinaryPrime.prime_separated _ _ hs

def graph (N : Network AlgebraicComplex 4) : Network AlgebraicComplex 4 :=
  P.network (paired reps q safe N) (1/2)

def coefficient : AlgebraicComplex := (1/2)^2*
  ((O.scalar (word reps q safe)*left reps q safe)^2-
    (O.scalar (word reps q safe)*right reps q safe)^2)

include prime in
theorem coefficient_nonzero : coefficient reps q safe≠0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (sub_ne_zero.mpr (separated reps q prime safe))

theorem graph_denote (N : Network AlgebraicComplex 4) (form : N.denote=T.H.symm.action q) :
    (graph reps q safe N).denote=coefficient reps q safe • Holant.EightVertex.ProductAnchor.equalityFour :=
  P.denote _ _ _ _ (paired_denote reps q safe N form)

theorem graph_ordinary (N : Network AlgebraicComplex 4) (input : ∀e,N.edge e=Signature.equality) :
    ∀e,(graph reps q safe N).edge e=Signature.equality :=
  P.ordinary _ _ (O.run_ordinary reps (word reps q safe) N input)

section Labels
variable {s : ℕ} {a : ℕ→ℕ} (H : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (z : Fin s) (zLiteral : (⟨a z.val,H z⟩ : AnySignature AlgebraicComplex)=
  ⟨2,GlobalCloseCompletionKleinOrdinaryAttach.binary GlobalCloseCompletionKleinOrdinaryHTransport.zHalf⟩)
variable (row : Fin 4→Fin s) (rowLiteral : ∀j,
  (⟨a (row j).val,H (row j)⟩ : AnySignature AlgebraicComplex)=
    ⟨2,GlobalCloseCompletionKleinOrdinaryAttach.binary (transport T.H (reps.matrix j))⟩)

def graphLabels (N : Network AlgebraicComplex 4) (L : Labelling N.shape s 1 a) :
    Labelling (graph reps q safe N).shape s 1 a :=
  P.labels H (paired reps q safe N)
    (LabelledNetwork.reindex _ (O.runLabels reps H z zLiteral row rowLiteral (word reps q safe) N L) P.pairOrder)
    z (1/2) zLiteral

theorem graph_exact (N : Network AlgebraicComplex 4) (L : Labelling N.shape s 1 a)
    (input : LabelledNetwork.Exact H N L) :
    LabelledNetwork.Exact H (graph reps q safe N)
      (graphLabels reps q safe H z zLiteral row rowLiteral N L) :=
  P.exact H _ _ z (1/2) zLiteral
    (O.run_exact reps H z zLiteral row rowLiteral (word reps q safe) N L input)
end Labels


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryExoticEq4
end
