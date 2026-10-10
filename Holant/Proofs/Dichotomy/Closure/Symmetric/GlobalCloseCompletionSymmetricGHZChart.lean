import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZField
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZEdgeSource
import Holant.Proofs.Algorithms.HolographicTransport

/-! A retained inverse-binary edge and an algebraic normalizing frame give a
genuine ordinary source on the complete transformed old table. The field is
generated internally, and both subdivision and answer codecs are composed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZChart
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace Fd
export GlobalCloseCompletionSymmetricGHZField (field presentation table constant constant_value table_value controlled)
end Fd
namespace E
export GlobalCloseCompletionSymmetricGHZEdgeSource (tables controlled)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (arity i.val))
variable (J : Kernel L) (R : InvertibleKernel)

def extras : Fin 12→AlgebraicComplex :=
  ![R.matrix false false,R.matrix false true,R.matrix true false,R.matrix true true,
    R.inverse false false,R.inverse false true,R.inverse true false,R.inverse true true,
    (J false false : AlgebraicComplex),(J false true : AlgebraicComplex),
    (J true false : AlgebraicComplex),(J true true : AlgebraicComplex)]
def slot (k : Fin 3) (p q : Bool) : Fin 12 :=
  ⟨4*k.val+(if p then 2 else 0)+(if q then 1 else 0),by have :=k.isLt; split_ifs <;> omega⟩
abbrev field:=Fd.field L H (extras L J R)
local instance : Algebra ℚ (field L H J R):=(field L H J R).algebra'
abbrev presentation:=Fd.presentation L H (extras L J R)
abbrev oldTable:=Fd.table L H (extras L J R)
def matrix : Kernel (field L H J R):=fun p q=>Fd.constant L H (extras L J R) (slot 0 p q)
def inverse : Kernel (field L H J R):=fun p q=>Fd.constant L H (extras L J R) (slot 1 p q)
def edge : Kernel (field L H J R):=fun p q=>Fd.constant L H (extras L J R) (slot 2 p q)

theorem matrix_value (p q : Bool) : (matrix L H J R p q : AlgebraicComplex)=R.matrix p q := by
  cases p <;> cases q <;> rfl
theorem inverse_value (p q : Bool) : (inverse L H J R p q : AlgebraicComplex)=R.inverse p q := by
  cases p <;> cases q <;> rfl
theorem edge_value (p q : Bool) : (edge L H J R p q : AlgebraicComplex)=(J p q : AlgebraicComplex) := by
  cases p <;> cases q <;> rfl

theorem map_matrix (p q : Bool) : (field L H J R).subtype (matrix L H J R p q)=R.matrix p q :=
  matrix_value L H J R p q
theorem map_inverse (p q : Bool) : (field L H J R).subtype (inverse L H J R p q)=R.inverse p q :=
  inverse_value L H J R p q
theorem map_edge (p q : Bool) : (field L H J R).subtype (edge L H J R p q)=(J p q : AlgebraicComplex) :=
  edge_value L H J R p q
theorem map_equality (p q : Bool) : (field L H J R).subtype (Signature.equality p q)=Signature.equality p q := by
  cases p <;> cases q <;> rfl

theorem matrix_inverse : Kernel.mul (matrix L H J R) (inverse L H J R)=Signature.equality := by
  funext p q
  apply (field L H J R).subtype.injective
  have h:=congrFun₂ R.matrix_inverse p q
  change (field L H J R).subtype (Kernel.mul (matrix L H J R) (inverse L H J R) p q)=_
  simp only [Kernel.mul,map_sum,map_mul,map_matrix,map_inverse]
  simpa [Kernel.mul,Signature.equality] using h

variable (normalized : Kernel.pullback (fun p q=>(J p q : AlgebraicComplex)) R.matrix=Signature.equality)

include normalized in
theorem edge_normalized : Kernel.pullback (edge L H J R) (matrix L H J R)=Signature.equality := by
  funext p q
  apply (field L H J R).subtype.injective
  have h:=congrFun₂ normalized p q
  change (field L H J R).subtype (Kernel.pullback (edge L H J R) (matrix L H J R) p q)=_
  simp only [Kernel.pullback,Kernel.mul,Kernel.transpose,map_sum,map_mul,map_matrix,map_edge]
  simpa [Kernel.pullback,Kernel.mul,Kernel.transpose,Signature.equality] using h

def table (i : Fin r) : Signature (field L H J R) (arity i.val):=
  Signature.coordinateAction (fun _=>inverse L H J R) (oldTable L H J R i)
abbrev tables:=QuaternaryOrdinaryCompanion.tables (presentation L H J R) (table L H J R)
abbrev edgeTables:=E.tables (presentation L H J R) (oldTable L H J R) (edge L H J R)
abbrev transformed:=HolographicTransport.tables (presentation L H J R) (edgeTables L H J R)
  (matrix L H J R) (inverse L H J R)

include normalized in
theorem transformed_tables : transformed L H J R=tables L H J R := by
  unfold transformed HolographicTransport.tables edgeTables E.tables tables QuaternaryOrdinaryCompanion.tables table
  simp only [LinearEquiv.apply_symm_apply]
  congr 1
  funext i p q
  rw [edge_normalized L H J R normalized]

theorem table_value (i : Fin r) (x : Fin (arity i.val)→Bool) :
    (table L H J R i x : AlgebraicComplex)=R.symm.action (fun y=>(H i y : AlgebraicComplex)) x := by
  change (field L H J R).subtype (Signature.coordinateAction (fun _=>inverse L H J R) (oldTable L H J R i) x)=_
  simp only [Signature.coordinateAction,map_sum,map_mul,map_prod,map_inverse]
  change (∑y,(∏i,R.inverse (x i) (y i))*(field L H J R).subtype (oldTable L H J R i y))=
    ∑y,(∏i,R.inverse (x i) (y i))*(H i y : AlgebraicComplex)
  apply Finset.sum_congr rfl
  intro y _
  congr 1

theorem table_literal (i : Fin r) :
    RingHomRealization.mapAny (field L H J R).subtype (⟨arity i.val,table L H J R i⟩ : AnySignature (field L H J R))=
      ⟨arity i.val,R.symm.action (fun x=>(H i x : AlgebraicComplex))⟩ :=
  congrArg (fun f : Signature AlgebraicComplex (arity i.val)=>(⟨arity i.val,f⟩ : AnySignature AlgebraicComplex))
    (funext (table_value L H J R i))

theorem retained_literal {n : ℕ} (i : Fin r) (f : Signature AlgebraicComplex n)
    (literal : RingHomRealization.mapAny L.subtype (⟨arity i.val,H i⟩ : AnySignature L)=⟨n,f⟩) :
    RingHomRealization.mapAny (field L H J R).subtype (⟨arity i.val,table L H J R i⟩ : AnySignature (field L H J R))=
      ⟨n,R.symm.action f⟩ :=
  (table_literal L H J R i).trans (congrArg
    (fun g : AnySignature AlgebraicComplex=>(⟨g.1,R.symm.action g.2⟩ : AnySignature AlgebraicComplex)) literal)

variable (j : Fin r) (literal : (⟨arity j.val,H j⟩ : AnySignature L)=⟨2,fun x=>J (x 0) (x 1)⟩)

include literal in
theorem edge_literal : (⟨arity j.val,oldTable L H J R j⟩ : AnySignature (field L H J R))=
    ⟨2,fun x=>edge L H J R (x 0) (x 1)⟩ := by
  have injective {K T : Type} [Field K] [Field T] (phi : K→+*T) : Function.Injective (RingHomRealization.mapAny phi) := by
    rintro ⟨n,f⟩ ⟨m,g⟩ h
    have ar : n=m:=congrArg Sigma.fst h
    subst m
    apply congrArg (fun q : Signature K n=>(⟨n,q⟩ : AnySignature K))
    funext x
    exact phi.injective (congrFun (eq_of_heq (Sigma.mk.inj_iff.mp h).2) x)
  apply injective (field L H J R).subtype
  have h:=congrArg (RingHomRealization.mapAny L.subtype) literal
  refine h.trans ?_
  apply congrArg (fun q : Signature AlgebraicComplex 2=>(⟨2,q⟩ : AnySignature AlgebraicComplex))
  funext x
  exact (edge_value L H J R (x 0) (x 1)).symm

def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 arity) (presentation L H J R).encoding
    (RawClosedNetwork.validatedEncoding r 1 arity) F.encoding
    ((tables L H J R).evaluate (presentation L H J R))
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) := by
  rw [←transformed_tables L H J R normalized]
  exact Programme.compose
    (HolographicTransport.fromTransformed (presentation L H J R) (edgeTables L H J R)
      (matrix L H J R) (inverse L H J R) (matrix_inverse L H J R))
    (Programme.compose (E.controlled (presentation L H J R) (oldTable L H J R) (edge L H J R)
      j (edge_literal L H J R j literal)) (Fd.controlled L F H (extras L J R)))

def family : SignatureFamily AlgebraicComplex:=Set.range fun i : Fin r=>
  RingHomRealization.mapAny (field L H J R).subtype (⟨arity i.val,table L H J R i⟩ : AnySignature (field L H J R))

theorem family_exact : family L H J R=familyAction R.symm (GlobalCloseCompletionUnaryDescentSource.ambient L H) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨⟨arity i.val,fun x=>(H i x : AlgebraicComplex)⟩,⟨i,rfl⟩,?_⟩
    apply congrArg (fun g : Signature AlgebraicComplex (arity i.val)=>(⟨arity i.val,g⟩ : AnySignature AlgebraicComplex))
    exact (funext (table_value L H J R i)).symm
  · rintro ⟨g,⟨i,rfl⟩,rfl⟩
    refine ⟨i,?_⟩
    apply congrArg (fun g : Signature AlgebraicComplex (arity i.val)=>(⟨arity i.val,g⟩ : AnySignature AlgebraicComplex))
    exact funext (table_value L H J R i)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZChart
end
