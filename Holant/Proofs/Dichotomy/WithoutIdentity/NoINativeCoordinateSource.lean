import Holant.Proofs.Dichotomy.Native.NativeTableFieldExtension
import Holant.Proofs.Algorithms.HolographicTransport

/-! A whole-family native-X coordinate change with a genuine common basis
preserving X. The finite field and answer-codec conversion are internal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeCoordinateSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace Fd
export NativeTableFieldExtension (field presentation table constant constant_value table_value controlled)
end Fd
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {r degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (arity i.val))
variable (R : InvertibleKernel)
def extras : Fin 8→AlgebraicComplex:=
  ![R.matrix false false,R.matrix false true,R.matrix true false,R.matrix true true,
    R.inverse false false,R.inverse false true,R.inverse true false,R.inverse true true]
def slot (k : Bool) (p q : Bool) : Fin 8:=
  ⟨(if k then 4 else 0)+(if p then 2 else 0)+(if q then 1 else 0),by split_ifs <;> decide⟩
abbrev field:=Fd.field L H (extras R)
local instance : Algebra ℚ (field L H R):=(field L H R).algebra'
abbrev presentation:=Fd.presentation L H (extras R)
abbrev oldTable:=Fd.table L H (extras R)
def matrix : Kernel (field L H R):=fun p q=>Fd.constant L H (extras R) (slot false p q)
def inverse : Kernel (field L H R):=fun p q=>Fd.constant L H (extras R) (slot true p q)
theorem matrix_value (p q : Bool) : (matrix L H R p q : AlgebraicComplex)=R.matrix p q := by
  cases p <;> cases q <;> rfl
theorem inverse_value (p q : Bool) : (inverse L H R p q : AlgebraicComplex)=R.inverse p q := by
  cases p <;> cases q <;> rfl

theorem map_matrix (p q : Bool) : (field L H R).subtype (matrix L H R p q)=R.matrix p q := matrix_value L H R p q
theorem map_inverse (p q : Bool) : (field L H R).subtype (inverse L H R p q)=R.inverse p q := inverse_value L H R p q
theorem map_x (p q : Bool) : (field L H R).subtype (Signature.disequality p q)=Signature.disequality p q := by
  cases p <;> cases q <;> rfl

theorem matrix_inverse : Kernel.mul (matrix L H R) (inverse L H R)=Signature.equality := by
  funext p q
  apply (field L H R).subtype.injective
  have h:=congrFun₂ R.matrix_inverse p q
  change (field L H R).subtype (Kernel.mul (matrix L H R) (inverse L H R) p q)=_
  simp only [Kernel.mul,map_sum,map_mul,map_matrix,map_inverse]
  simpa [Kernel.mul,Signature.equality] using h

variable (native : Kernel.pullback Signature.disequality R.matrix=Signature.disequality)
include native in
theorem edge_exact : Kernel.pullback Signature.disequality (matrix L H R)=Signature.disequality := by
  funext p q
  apply (field L H R).subtype.injective
  have h:=congrFun₂ native p q
  change (field L H R).subtype (Kernel.pullback Signature.disequality (matrix L H R) p q)=_
  simp only [Kernel.pullback,Kernel.mul,Kernel.transpose,map_sum,map_mul,map_matrix,map_x]
  have hx (x y : Bool) : (field L H R).subtype (Signature.disequality x y)=Signature.disequality x y := by
    cases x <;> cases y <;> rfl
  cases p <;> cases q <;> simpa [Kernel.pullback,Kernel.mul,Kernel.transpose,Signature.disequality] using h

def table (i : Fin r) : Signature (field L H R) (arity i.val):=
  Signature.coordinateAction (fun _=>inverse L H R) (oldTable L H R i)
abbrev tables:=NativeAntiTargetSource.base (table L H R) (presentation L H R)
abbrev oldTables:=NativeAntiTargetSource.base (oldTable L H R) (presentation L H R)
abbrev transformed:=HolographicTransport.tables (presentation L H R) (oldTables L H R)
  (matrix L H R) (inverse L H R)
include native in
theorem transformed_tables : transformed L H R=tables L H R := by
  unfold transformed HolographicTransport.tables oldTables tables NativeAntiTargetSource.base table
  simp only [LinearEquiv.apply_symm_apply]
  congr 1
  funext i p q
  rw [edge_exact L H R native]

def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 arity) (presentation L H R).encoding
    (RawClosedNetwork.validatedEncoding r 1 arity) F.encoding
    ((tables L H R).evaluate (presentation L H R)) ((NativeAntiTargetSource.base H F).evaluate F) := by
  rw [←transformed_tables L H R native]
  exact Programme.compose
    (HolographicTransport.fromTransformed (presentation L H R) (oldTables L H R)
      (matrix L H R) (inverse L H R) (matrix_inverse L H R))
    (Fd.controlled L F H (extras R))

theorem table_value (i : Fin r) (x : Fin (arity i.val)→Bool) :
    (table L H R i x : AlgebraicComplex)=R.symm.action (fun y=>(H i y : AlgebraicComplex)) x := by
  change (field L H R).subtype (Signature.coordinateAction (fun _=>inverse L H R) (oldTable L H R i) x)=_
  simp only [Signature.coordinateAction,map_sum,map_mul,map_prod,map_inverse]
  change (∑y,(∏i,R.inverse (x i) (y i))*(field L H R).subtype (oldTable L H R i y))=
    ∑y,(∏i,R.inverse (x i) (y i))*(H i y : AlgebraicComplex)
  apply Finset.sum_congr rfl
  intro y _
  congr 1


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoINativeCoordinateSource
end
