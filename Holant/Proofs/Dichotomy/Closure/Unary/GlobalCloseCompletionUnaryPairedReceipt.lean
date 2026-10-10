import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryStructuralSource
import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesComplete

/-! The universal unary selector's adjacent-paired graph enters the strict
paired-series consumer with its actual scalar pin0 and unchanged full table.
The returned Eq4 receipt retains every literal old row and its programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPairedReceipt
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
namespace S
export GlobalCloseCompletionUnaryStructuralSource (PinSource)
end S
namespace Q
export GlobalCloseCompletionUnaryQuaternaryForm (Paired determinant)
end Q
namespace P
export GlobalCloseCompletionPairedSeriesCore (row)
export GlobalCloseCompletionPairedSeriesComplete (produce)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (src : S.PinSource G)
local instance : Algebra ℚ src.K:=src.K.algebra'
local instance : CharZero src.K:=Algebra.charZero_of_charZero ℚ src.K
variable (N : NoXOrdinaryGraphAdjoin.Output src.table 4)
variable (support : Q.Paired N.network.denote) (nonsingular : Q.determinant N.network.denote≠0)

def matrix : Matrix Bool Bool src.K := fun p q=>N.network.denote ![p,p,q,q]

def graph : Macro src.table 4 :=
  (show Macro src.table 4 from ⟨N.network,N.labels,N.exact,N.ordinary⟩).reindex (Equiv.swap 1 2)
def first : Macro src.table 1 :=
  ⟨src.first.network,src.first.labels,src.first.exact,src.first.ordinary⟩

include support in
theorem form : (graph G src N).network.denote=P.row (matrix G src N) := by
  rw [graph,Macro.reindex_denote]
  funext x
  change N.network.denote (fun i=>x ((Equiv.swap 1 2) i))=P.row (matrix G src N) x
  have word : (fun i=>x ((Equiv.swap (1 : Fin 4) 2) i))=![x 0,x 2,x 1,x 3] := by
    funext i;fin_cases i <;>rfl
  rw [word]
  cases h0 : x 0 <;>cases h1 : x 1 <;>cases h2 : x 2 <;>cases h3 : x 3 <;>
    simp [P.row,matrix,h0,h1,h2,h3]
  all_goals apply support <;>simp

include nonsingular in
theorem determinant : (matrix G src N).det≠0 := by
  rw [Holant.Complexity.BinaryInterpolation.det_entries]
  exact nonsingular

def phi : src.K→+*ℂ := (algebraicClosure ℚ ℂ).subtype.comp src.K.subtype

def receipt : GlobalCloseCompletionPairedSeriesReceipt.Receipt src.table src.F :=
  P.produce src.table src.F (phi G src) (graph G src N) (matrix G src N)
    (form G src N support) (determinant G src N nonsingular)
    (first G src) src.scalar src.nonzero src.pin0 src.pin1

theorem old_included : GlobalCloseCompletionUnaryDescentSource.ambient src.K src.table⊆
    GlobalCloseCompletionUnaryDescentSource.ambient src.K (receipt G src N support nonsingular).table := by
  rintro f ⟨i,rfl⟩
  exact ⟨(receipt G src N support nonsingular).old i,
    congrArg (RingHomRealization.mapAny src.K.subtype) ((receipt G src N support nonsingular).old_literal i)⟩

theorem obstruction : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient src.K
    (receipt G src N support nonsingular).table) :=
  fun h=>src.negative (h.mono_family (old_included G src N support nonsingular))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPairedReceipt
end
