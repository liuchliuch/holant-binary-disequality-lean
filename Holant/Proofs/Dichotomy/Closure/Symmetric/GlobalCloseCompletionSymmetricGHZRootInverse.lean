import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZRootInverseField

/-! A nonzero semisimple actual ordinary binary has an implemented scalar
inverse source. The scalar case uses the same graph; the distinct-root case
derives and lifts the two algebraic roots before the finite/infinite chain
dispatch. Both the complete old table and the original binary macro survive. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZRootInverse
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
open OrdinaryNegativeCubicGadgets
namespace R
export GlobalCloseCompletionSymmetricGHZRootInverseField
  (Roots roots extra field presentation table graph matrix_value extension)
end R
namespace Fld
export GlobalCloseCompletionSymmetricGHZField (controlled)
end Fld
namespace I
export GlobalCloseCompletionSymmetricGHZInverse (matrix)
end I
namespace C
export GlobalCloseCompletionSymmetricGHZCapSelection (discriminant Semisimple)
end C
namespace A
export NoXOrdinaryGraphAdjoin (Output arity signatures source old old_literal newLabel new_literal)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false

local instance matrixScalar (K : IntermediateField ℚ AlgebraicComplex) : SMul K (Binary (K:=K)) where
  smul c M i j:=c*M i j

section Relabel
variable {K : Type} [Field K] [Algebra ℚ K] {r t n : ℕ} {b c : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (b i.val)) (T : (i : Fin t)→Signature K (c i.val))
variable (labels : Fin r→Fin t)
variable (literal : ∀i,(⟨c (labels i).val,T (labels i)⟩ : AnySignature K)=⟨b i.val,H i⟩)

def relabel (N : A.Output H n) : A.Output T n where
  network:=N.network
  labels:={
    vertex v:=labels (N.labels.vertex v)
    vertex_arity v:=(congrArg Sigma.fst (literal (N.labels.vertex v))).trans (N.labels.vertex_arity v)
    edge _:=0 }
  exact v:=(literal (N.labels.vertex v)).trans (N.exact v)
  ordinary:=N.ordinary
end Relabel

variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (N : A.Output H 2)

structure Extension : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  presentation : letI : Algebra ℚ K:=K.algebra';FixedField K degree
  count : ℕ
  arity : ℕ→ℕ
  table : (i : Fin count)→Signature K (arity i.val)
  old : Fin r→Fin count
  old_literal : ∀i,RingHomRealization.mapAny K.subtype (⟨arity (old i).val,table (old i)⟩ : AnySignature K)=
    RingHomRealization.mapAny L.subtype (⟨b i.val,H i⟩ : AnySignature L)
  original : Binary (K:=K)
  original_value : original.map (K.val.toRingHom : K→+*AlgebraicComplex)=
    (I.matrix H N).map (L.val.toRingHom : L→+*AlgebraicComplex)
  originalGraph : letI : Algebra ℚ K:=K.algebra';A.Output table 2
  original_form : originalGraph.network.denote=binarySignature original
  inverse : Binary (K:=K)
  scalar : K
  nonzero : scalar≠0
  label : Fin count
  literal : (⟨arity label.val,table label⟩ : AnySignature K)=⟨2,binarySignature inverse⟩
  left_inverse : inverse*original=scalar • (1 : Binary (K:=K))
  right_inverse : original*inverse=scalar • (1 : Binary (K:=K))
  source : letI : Algebra ℚ K:=K.algebra';LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) presentation.encoding
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    ((QuaternaryOrdinaryCompanion.tables presentation table).evaluate presentation)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)

def scalar (c : L) (hc : c≠0) (form : I.matrix H N=c • (1 : Binary (K:=L))) : Extension L F H N where
  K:=L
  degree:=degree
  presentation:=F
  count:=r+1
  arity:=A.arity H N
  table:=A.signatures F H N
  old:=A.old H
  old_literal i:=congrArg (RingHomRealization.mapAny L.subtype) (A.old_literal F H N i)
  original:=I.matrix H N
  original_value:=rfl
  originalGraph:=relabel H (A.signatures F H N) (A.old H) (A.old_literal F H N) N
  original_form:=(binarySignature_binaryMatrix _).symm
  inverse:=I.matrix H N
  scalar:=c^2
  nonzero:=pow_ne_zero _ hc
  label:=A.newLabel H
  literal:=(A.new_literal F H N).trans (congrArg (fun f : Signature L 2=>(⟨2,f⟩ : AnySignature L))
    (binarySignature_binaryMatrix _).symm)
  left_inverse:=by
    rw [form]
    ext i j
    cases i <;> cases j <;> simp [matrixScalar,Matrix.mul_apply,Matrix.one_apply,Fintype.sum_bool,pow_two]
  right_inverse:=by
    rw [form]
    ext i j
    cases i <;> cases j <;> simp [matrixScalar,Matrix.mul_apply,Matrix.one_apply,Fintype.sum_bool,pow_two]
  source:=A.source F H N

def distinct (roots : R.Roots L H N) : Extension L F H N := by
  let K:=R.field L H N roots
  letI : Algebra ℚ K:=K.algebra'
  let D:=R.extension L H N roots
  exact {
    K:=K
    degree:=Module.finrank ℚ K
    presentation:=R.presentation L H N roots
    count:=D.count
    arity:=D.b
    table:=D.table
    old:=D.old
    old_literal:=by
      intro i
      exact (congrArg (RingHomRealization.mapAny K.subtype) (D.old_literal i)).trans rfl
    original:=I.matrix (R.table L H N roots) (R.graph L H N roots)
    original_value:=R.matrix_value L H N roots
    originalGraph:=relabel (R.table L H N roots) D.table D.old D.old_literal (R.graph L H N roots)
    original_form:=(binarySignature_binaryMatrix _).symm
    inverse:=D.inverse
    scalar:=D.scalar
    nonzero:=D.nonzero
    label:=D.label
    literal:=D.literal
    left_inverse:=D.left_inverse
    right_inverse:=D.right_inverse
    source:=Programme.compose D.source (Fld.controlled L F H (R.extra L H N roots)) }

def produce (det : Matrix.det (I.matrix H N)≠0) (semisimple : C.Semisimple (I.matrix H N)) :
    Extension L F H N := by
  classical
  by_cases discriminant : C.discriminant (I.matrix H N)≠0
  · exact distinct L F H N (R.roots L H N det discriminant)
  · have scalarExists : ∃c : L,c≠0 ∧ I.matrix H N=c • (1 : Binary (K:=L)):=semisimple.resolve_left discriminant
    exact scalar L F H N scalarExists.choose scalarExists.choose_spec.1 scalarExists.choose_spec.2

variable (D : Extension L F H N)
local instance : Algebra ℚ D.K:=D.K.algebra'

def originalMacro : Macro D.table 2 :=
  ⟨D.originalGraph.network,D.originalGraph.labels,D.originalGraph.exact,D.originalGraph.ordinary⟩

theorem mapped_left : D.inverse.map (D.K.val.toRingHom : D.K→+*AlgebraicComplex)*
    (I.matrix H N).map (L.val.toRingHom : L→+*AlgebraicComplex)=
    (D.scalar : AlgebraicComplex) • (1 : Binary (K:=AlgebraicComplex)) := by
  rw [←D.original_value,←Matrix.map_mul,D.left_inverse]
  ext i j
  cases i <;> cases j <;> simp [Matrix.map_apply,Matrix.one_apply]

theorem mapped_right : (I.matrix H N).map (L.val.toRingHom : L→+*AlgebraicComplex)*
    D.inverse.map (D.K.val.toRingHom : D.K→+*AlgebraicComplex)=
    (D.scalar : AlgebraicComplex) • (1 : Binary (K:=AlgebraicComplex)) := by
  rw [←D.original_value,←Matrix.map_mul,D.right_inverse]
  ext i j
  cases i <;> cases j <;> simp [Matrix.map_apply,Matrix.one_apply]

theorem original_graph_value :
    RingHomRealization.mapSignature D.K.subtype D.originalGraph.network.denote=
      RingHomRealization.mapSignature L.subtype N.network.denote := by
  rw [D.original_form]
  have h:=congrArg binarySignature D.original_value
  have original : binarySignature (I.matrix H N)=N.network.denote:=binarySignature_binaryMatrix _
  funext x
  change D.K.subtype (binarySignature D.original x)=L.subtype (N.network.denote x)
  rw [←original]
  exact congrFun h x


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZRootInverse
end
