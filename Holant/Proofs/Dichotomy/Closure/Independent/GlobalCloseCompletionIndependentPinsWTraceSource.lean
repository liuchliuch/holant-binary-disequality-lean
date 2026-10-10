import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWTraceCore
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsSymmetricSource
import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZSource

/-! Arbitrary W-orbit ternaries, not only symmetric ones, have a genuine
same-table symmetric GHZ producer with a retained nonsingular symmetric trace-zero phase. Three cyclic orientations
and the two physical equality/phase choices are selected internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWTraceSource
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization OrdinaryNegativeCubicGadgets
namespace W
export GlobalCloseCompletionIndependentPinsWGeneralCore
  (image gram triangle_image gram_determinant core_basis)
end W
namespace X
export GlobalCloseCompletionIndependentPinsWTraceCore (gram triangle_image gram_determinant choose_pair twist)
end X
namespace Trace
export GlobalCloseCompletionSymmetricGHZTrace (binary)
end Trace
namespace G
export GlobalCloseCompletionIndependentPinsWGraph (graph graph_mapped map_triangle decorate order)
end G
namespace R
export GlobalCloseCompletionTernaryGHZSource (rotate rotate_value)
end R
namespace Forms
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz)
end Forms
namespace S
export GlobalCloseCompletionIndependentPinsSymmetricSource (Output)
end S
namespace T
export GlobalCloseCompletionTernaryGHZCore (cyclic)
end T
namespace Z
export GlobalCloseCompletionUnaryIsotropicSource (z)
end Z
namespace Alg
export Holant.Tractable.SymmetricBinaryPullback (determinant_ne_zero)
end Alg
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {b : ℕ→ℕ}
variable (phi : K→+*AlgebraicComplex) (H : (i : Fin r)→Signature K (b i.val))
variable (N : Macro H 3) (D : Macro H 2) (a c : AlgebraicComplex)
variable (traceForm : RingHomRealization.mapSignature phi D.network.denote=Trace.binary a c c)
variable (phase : -a^2-c*c≠0)

include traceForm in
theorem decorate_mapped :
    RingHomRealization.mapSignature phi (G.decorate N D).network.denote=
      X.twist a c (RingHomRealization.mapSignature phi N.network.denote) := by
  funext z
  rw [RingHomRealization.mapSignature,G.decorate,Macro.contract_denote]
  simp only [Macro.reindex_denote,Macro.tensor_denote,Tensor.reindex_apply,Signature.tensor_apply]
  have first (v : Bool) :
      (fun i : Fin 3=>(Fin.cons v (Fin.cons v z) : Fin 5→Bool) (G.order (Fin.castAdd 2 i)))=![z 0,v,z 2] := by
    funext i
    fin_cases i <;> rfl
  have second (v : Bool) :
      (fun i : Fin 2=>(Fin.cons v (Fin.cons v z) : Fin 5→Bool) (G.order (Fin.natAdd 3 i)))=![v,z 1] := by
    funext i
    fin_cases i <;> rfl
  simp only [first,second,map_add,map_mul]
  have hd (v : Bool) : phi (D.network.denote ![v,z 1])=Trace.binary a c c ![v,z 1]:=
    congrFun traceForm ![v,z 1]
  simp only [hd,X.twist,RingHomRealization.mapSignature,Trace.binary,
    Matrix.cons_val_zero,Matrix.cons_val_one,Bool.false_eq_true,ite_false,ite_true]

theorem rotate_image (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote=W.image A.matrix B.matrix C.matrix) :
    RingHomRealization.mapSignature phi (R.rotate N).network.denote=W.image C.matrix A.matrix B.matrix := by
  funext x
  rw [RingHomRealization.mapSignature,R.rotate_value]
  have h:=congrFun form (T.cyclic x)
  change phi (N.network.denote (T.cyclic x))=_ at h
  rw [h]
  simp [W.image,T.cyclic]
  ring

include traceForm phase in
theorem good_triangle (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote=W.image A.matrix B.matrix C.matrix)
    (v : Bool) (good : (if v then X.gram a c B.matrix C.matrix false false else W.gram 1 B.matrix C.matrix false false)≠0) :
    ∃Q : InvertibleKernel,RingHomRealization.mapSignature phi (G.graph N D v).network.denote=Forms.ghz Q.matrix := by
  cases v with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at good
    have det : W.gram 1 B.matrix C.matrix false false*W.gram 1 B.matrix C.matrix true true-
        W.gram 1 B.matrix C.matrix false true*W.gram 1 B.matrix C.matrix true false≠0 := by
      rw [W.gram_determinant,one_mul]
      exact mul_ne_zero (Alg.determinant_ne_zero B) (Alg.determinant_ne_zero C)
    obtain ⟨Q,hQ⟩:=W.core_basis _ _ _ _ good det
    refine ⟨A.comp Q,?_⟩
    rw [G.graph,if_neg Bool.false_ne_true,GlobalCloseCompletionTernaryGHZGraph.value,G.map_triangle,form]
    have one : GlobalCloseCompletionIndependentPinsWCore.twist (1:AlgebraicComplex) (W.image A.matrix B.matrix C.matrix)=W.image A.matrix B.matrix C.matrix := by
      funext z
      simp [GlobalCloseCompletionIndependentPinsWCore.twist,GlobalCloseCompletionIndependentPinsWCore.sign]
    rw [←one,W.triangle_image,←GlobalCloseCompletionIndependentPinsWCore.coordinate,hQ]
    exact Signature.coordinateAction_comp _ _ _
  | true =>
    simp only [ite_true] at good
    have det : X.gram a c B.matrix C.matrix false false*X.gram a c B.matrix C.matrix true true-
        X.gram a c B.matrix C.matrix false true*X.gram a c B.matrix C.matrix true false≠0 := by
      rw [X.gram_determinant]
      exact mul_ne_zero (mul_ne_zero phase (Alg.determinant_ne_zero B)) (Alg.determinant_ne_zero C)
    obtain ⟨Q,hQ⟩:=W.core_basis _ _ _ _ good det
    refine ⟨A.comp Q,?_⟩
    rw [G.graph,if_pos rfl,GlobalCloseCompletionTernaryGHZGraph.value,G.map_triangle,decorate_mapped phi H N D a c traceForm,form,
      X.triangle_image,←GlobalCloseCompletionIndependentPinsWCore.coordinate,hQ]
    exact Signature.coordinateAction_comp _ _ _

include D traceForm phase in
theorem exists_output (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote=W.image A.matrix B.matrix C.matrix) :
    Nonempty (S.Output phi H) := by
  rcases X.choose_pair a c phase A.matrix B.matrix C.matrix
    (Alg.determinant_ne_zero A) (Alg.determinant_ne_zero B) (Alg.determinant_ne_zero C) with bc|ab|ca
  · obtain ⟨v,hv⟩:=bc
    obtain ⟨Q,hQ⟩:=good_triangle phi H N D a c traceForm phase A B C form v hv
    exact ⟨⟨G.graph N D v,Q,hQ⟩⟩
  · obtain ⟨v,hv⟩:=ab
    obtain ⟨Q,hQ⟩:=good_triangle phi H (R.rotate N) D a c traceForm phase C A B (rotate_image phi H N A B C form) v hv
    exact ⟨⟨G.graph (R.rotate N) D v,Q,hQ⟩⟩
  · obtain ⟨v,hv⟩:=ca
    obtain ⟨Q,hQ⟩:=good_triangle phi H (R.rotate (R.rotate N)) D a c traceForm phase B C A
      (rotate_image phi H (R.rotate N) C A B (rotate_image phi H N A B C form)) v hv
    exact ⟨⟨G.graph (R.rotate (R.rotate N)) D v,Q,hQ⟩⟩

def produce (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote=W.image A.matrix B.matrix C.matrix) :
    S.Output phi H := Classical.choice (exists_output phi H N D a c traceForm phase A B C form)

include D traceForm phase in
theorem ghz_output (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote=GlobalCloseCompletionTernaryGHZCore.ghz A.matrix B.matrix C.matrix)
    (prime : Prime (⟨3,RingHomRealization.mapSignature phi N.network.denote⟩ : AnySignature AlgebraicComplex)) :
    Nonempty (S.Output phi H) := by
  obtain ⟨Q,primeQ,v,hv⟩:=GlobalCloseCompletionTernaryGHZSource.produce phi N A B C form prime
  have values : GlobalCloseCompletionTernaryGHZSymmetry.values (GlobalCloseCompletionTernaryGHZSymmetry.symmetric v)=v := by
    funext i
    fin_cases i <;> rfl
  have symmetry : RingHomRealization.mapSignature phi Q.network.denote=
      GlobalCloseCompletionTernaryGHZSymmetry.symmetric
        (GlobalCloseCompletionTernaryGHZSymmetry.values (RingHomRealization.mapSignature phi Q.network.denote)) := by
    rw [hv,values]
  rcases GlobalCloseCompletionIndependentPinsSymmetricDecomposition.symmetric_prime
    (RingHomRealization.mapSignature phi Q.network.denote) symmetry primeQ with ghz|w
  · obtain ⟨R,hR⟩:=ghz
    exact ⟨⟨Q,R,hR⟩⟩
  · obtain ⟨R,hR⟩:=w
    have formW : RingHomRealization.mapSignature phi Q.network.denote=W.image R.matrix R.matrix R.matrix := by
      rw [hR]
      exact (GlobalCloseCompletionIndependentPinsWCore.image_eq R.matrix).symm
    exact exists_output phi H Q D a c traceForm phase R R R formW


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWTraceSource
end
