import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZField
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets

/-! Transport an actual ordinary graph along an exact ambient finite-family
inclusion. This handles coefficient-field changes introduced by the existing
Eq4/pin source; every old vertex is assigned an actual target label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZLift
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open OrdinaryNegativeCubicGadgets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r t n : ℕ} {a b : ℕ→ℕ}
variable (K L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature K (a i.val)) (S : (i : Fin t)→Signature L (b i.val))
def familyK : SignatureFamily AlgebraicComplex:=Set.range fun i : Fin r=>
  RingHomRealization.mapAny K.subtype (⟨a i.val,H i⟩ : AnySignature K)
def familyL : SignatureFamily AlgebraicComplex:=Set.range fun i : Fin t=>
  RingHomRealization.mapAny L.subtype (⟨b i.val,S i⟩ : AnySignature L)
variable (included : familyK K H⊆familyL L S) (N : Macro H n)

include included in
theorem member (v : Fin N.network.shape.vertices) :
    (⟨N.network.shape.arity v,RingHomRealization.mapSignature K.subtype (N.network.vertex v)⟩ : AnySignature AlgebraicComplex)∈
      familyL L S := by
  apply included
  refine ⟨N.labels.vertex v,?_⟩
  exact congrArg (RingHomRealization.mapAny K.subtype) (N.exact v)

def label (v : Fin N.network.shape.vertices) : Fin t:=(member K L H S included N v).choose
theorem label_exact (v : Fin N.network.shape.vertices) :
    RingHomRealization.mapAny L.subtype (⟨b (label K L H S included N v).val,S (label K L H S included N v)⟩ : AnySignature L)=
      ⟨N.network.shape.arity v,RingHomRealization.mapSignature K.subtype (N.network.vertex v)⟩ :=
  (member K L H S included N v).choose_spec
def labels : Labelling N.network.shape t 1 b where
  vertex:=label K L H S included N
  vertex_arity v:=congrArg Sigma.fst (label_exact K L H S included N v)
  edge _:=0
def network : Network L n:=(labels K L H S included N).sourceNetwork S (fun _ : Fin 1=>Signature.equality)

private theorem exact_cast {A : Type} {m n : ℕ} (f : Signature A m) (g : Signature A n)
    (h : (⟨m,f⟩ : AnySignature A)=⟨n,g⟩) (hn : m=n) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast hn i))=g x := by cases h; rfl

theorem map_network : (network K L H S included N).map L.subtype=N.network.map K.subtype := by
  unfold network Network.map Labelling.sourceNetwork
  congr 1
  · funext v x
    exact exact_cast _ _ (label_exact K L H S included N v)
      ((labels K L H S included N).vertex_arity v) x
  · funext e p q
    rw [N.edges]
    cases p <;> cases q <;> rfl

def lift : Macro S n where
  network:=network K L H S included N
  labels:=labels K L H S included N
  exact:=by
    intro v
    apply Sigma.ext ((labels K L H S included N).vertex_arity v)
    exact HEq.symm (EdgeSubdivision.signature_cast_heq ((labels K L H S included N).vertex_arity v)
      (S ((labels K L H S included N).vertex v)))
  edges:=fun _=>rfl

theorem value : RingHomRealization.mapSignature L.subtype (lift K L H S included N).network.denote=
    RingHomRealization.mapSignature K.subtype N.network.denote := by
  funext x
  change L.subtype ((network K L H S included N).denote x)=K.subtype (N.network.denote x)
  rw [←Network.denote_map,←Network.denote_map,map_network]

theorem trace_value (Q : Macro H 2) :
    (L.val.toRingHom : L→+*AlgebraicComplex) (Matrix.trace (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix
      (lift K L H S included Q).network.denote))=
    (K.val.toRingHom : K→+*AlgebraicComplex) (Matrix.trace (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix Q.network.denote)) := by
  simp only [Matrix.trace,map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact congrFun (value K L H S included Q) ![p,p]

theorem determinant_value (Q : Macro H 2) :
    (L.val.toRingHom : L→+*AlgebraicComplex) (Matrix.det (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix
      (lift K L H S included Q).network.denote))=
    (K.val.toRingHom : K→+*AlgebraicComplex) (Matrix.det (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix Q.network.denote)) := by
  have entry (p q : Bool) :
      (L.val.toRingHom : L→+*AlgebraicComplex) ((lift K L H S included Q).network.denote ![p,q])=
      (K.val.toRingHom : K→+*AlgebraicComplex) (Q.network.denote ![p,q]) :=
    congrFun (value K L H S included Q) ![p,q]
  simp only [Holant.Complexity.BinaryInterpolation.det_entries,map_sub,map_mul,
    Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix]
  exact congrArg₂ (fun x y : AlgebraicComplex=>x-y)
    (congrArg₂ (fun x y : AlgebraicComplex=>x*y) (entry false false) (entry true true))
    (congrArg₂ (fun x y : AlgebraicComplex=>x*y) (entry false true) (entry true false))

theorem trace_zero (Q : Macro H 2)
    (h : Matrix.trace (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix Q.network.denote)=0) :
    Matrix.trace (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix (lift K L H S included Q).network.denote)=0 := by
  apply (L.val.toRingHom : L→+*AlgebraicComplex).injective
  have hv:=trace_value K L H S included Q
  rw [h,map_zero] at hv
  exact hv.trans (map_zero _).symm

theorem determinant_nonzero (Q : Macro H 2)
    (h : Matrix.det (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix Q.network.denote)≠0) :
    Matrix.det (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix (lift K L H S included Q).network.denote)≠0 := by
  intro zero
  apply h
  apply (K.val.toRingHom : K→+*AlgebraicComplex).injective
  have hv:=determinant_value K L H S included Q
  rw [zero,map_zero] at hv
  exact hv.symm.trans (map_zero _).symm


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZLift
end
