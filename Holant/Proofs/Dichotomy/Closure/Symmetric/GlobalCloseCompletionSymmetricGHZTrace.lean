import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZEquality
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsAdjoin
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiComplete

/-! An actual nonsingular trace-zero binary closes an arbitrary ordinary
Eq4/two-pin source. Row and column caps give a real scalar Z graph whenever
a diagonal and an off-diagonal entry survive. The remaining zero-diagonal
case is the already proved weighted-antidiagonal terminal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZTrace
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
namespace A
export GlobalCloseCompletionIndependentPinsAdjoin
  (Output arity signatures old old_literal newLabel normalized_literal source)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def binary (a b c : K) : Signature K 2 := fun x=>
  if x 0 then (if x 1 then -a else c) else (if x 1 then b else a)

section Graph
variable {r : ℕ} {b : ℕ→ℕ} (H : (i : Fin r)→Signature K (b i.val))
variable (E : Macro H 4) (P : Bool→Macro H 1)
variable (eq4 : E.network.denote=Holant.EightVertex.ProductAnchor.equalityFour)
variable (pins : ∀v,(P v).network.denote=QuaternaryUnaryAccess.pin v)

def transpose (N : Macro H 2) : Macro H 2 := N.reindex (Equiv.swap 0 1)
def row (N : Macro H 2) (v : Bool) : Macro H 1 := ((P v).tensor N).contract
def column (N : Macro H 2) (v : Bool) : Macro H 1 := row H P (transpose H N) v
def sign (N : Macro H 2) : Macro H 2 :=
  ((column H P N true).tensor (((row H P N false).tensor E).contract)).contract

include pins in
theorem row_value (N : Macro H 2) (v : Bool) (x : Fin 1→Bool) :
    (row H P N v).network.denote x=N.network.denote ![v,x 0] := by
  rw [row,Macro.contract_denote,Macro.tensor_denote,pins]
  cases v <;> simp [Signature.tensor_apply,QuaternaryUnaryAccess.pin]
  all_goals congr 1; funext i; fin_cases i <;> rfl

include pins in
theorem column_value (N : Macro H 2) (v : Bool) (x : Fin 1→Bool) :
    (column H P N v).network.denote x=N.network.denote ![x 0,v] := by
  rw [column,row_value H P pins,transpose,Macro.reindex_denote]
  apply congrArg N.network.denote
  funext i
  fin_cases i <;> rfl

include eq4 pins in
theorem sign_value (N : Macro H 2) (a b c : K) (form : N.network.denote=binary a b c) :
    (sign H E P N).network.denote=fun x=>a*b*NoXGeneralZSign.signature x := by
  funext x
  rw [sign,Macro.contract_denote,Macro.tensor_denote]
  simp only [Signature.tensor_apply]
  simp_rw [column_value H P pins,Macro.contract_denote,Macro.tensor_denote,
    Signature.tensor_apply,row_value H P pins,eq4,form]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [binary,NoXGeneralZSign.signature,Holant.EightVertex.ProductAnchor.equalityFour,
      Fin.forall_fin_succ,h0,h1] <;> ring

theorem transpose_value (N : Macro H 2) (a b c : K) (form : N.network.denote=binary a b c) :
    (transpose H N).network.denote=binary a c b := by
  rw [transpose,Macro.reindex_denote,form]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Tensor.reindex,binary,Equiv.swap_apply_def,h0,h1]

def output {n : ℕ} (N : Macro H n) : A.Output H n :=
  ⟨N.network,N.labels,N.exact,N.edges⟩
end Graph

section Original
variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'

def equality : Macro src.H 4 := Macro.row src.e _ src.he
def pin (v : Bool) : Macro src.H 1 := Macro.row (src.p v) _ (src.hp v)

def normalized {n : ℕ} (N : Macro src.H n) (c : src.K) (nonzero : c≠0) : GenericOrdinarySource.Data G where
  K := src.K
  degree := src.degree
  F := src.F
  size := src.size+1
  b := A.arity src.H (output src.H N)
  H := A.signatures src.F src.H (output src.H N) c
  e := A.old src.H src.e
  p v := A.old src.H (src.p v)
  he := (A.old_literal src.F src.H (output src.H N) c src.e).trans src.he
  hp v := (A.old_literal src.F src.H (output src.H N) c (src.p v)).trans (src.hp v)
  toOriginal := Programme.compose (A.source src.F src.H (output src.H N) c nonzero) src.toOriginal

theorem old_included {n : ℕ} (N : Macro src.H n) (c : src.K) (nonzero : c≠0) :
    GenericOrdinarySource.family G src⊆GenericOrdinarySource.family G (normalized G src N c nonzero) := by
  rintro f ⟨i,rfl⟩
  refine ⟨A.old src.H i,?_⟩
  exact congrArg (RingHomRealization.mapAny src.K.subtype)
    (A.old_literal src.F src.H (output src.H N) c i)

theorem of_sign (N : Macro src.H 2) (c : src.K) (nonzero : c≠0)
    (form : N.network.denote=fun x=>c*NoXGeneralZSign.signature x) :
    Tract (GenericOrdinarySource.family G src) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  let next:=normalized G src N c nonzero
  have literal : (⟨next.b (A.newLabel src.H).val,next.H (A.newLabel src.H)⟩ : AnySignature next.K)=
      ⟨2,NoXGeneralZSign.signature⟩ :=
    A.normalized_literal src.F src.H (output src.H N) c _ nonzero form
  by_cases positive : Tract (GenericOrdinarySource.family G next)
  · exact Or.inl (positive.mono_family (old_included G src N c nonzero))
  · exact Or.inr (NoXGeneralComplete.countingHard G next (A.newLabel src.H) literal
      ((GenericOrdinarySource.rejected_iff G next).mp positive))

theorem classified (N : Macro src.H 2) (a b c : src.K)
    (form : N.network.denote=binary a b c) (determinant : -a^2-b*c≠0) :
    Tract (GenericOrdinarySource.family G src) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_cases ha : a=0
  · have bc : b*c≠0 := by simpa [ha] using determinant
    have nonzeroB := (mul_ne_zero_iff.mp bc).1
    have nonzeroC := (mul_ne_zero_iff.mp bc).2
    let next:=NoXOrdinaryGraphSource.data G src (output src.H N)
    have literal : (⟨next.b (A.newLabel src.H).val,next.H (A.newLabel src.H)⟩ : AnySignature next.K)=
        ⟨2,NoXWeightedAntiSigned.anti b c⟩ := by
      refine (NoXOrdinaryGraphSource.new_literal G src (output src.H N)).trans ?_
      apply congrArg (fun f : Signature src.K 2=>(⟨2,f⟩ : AnySignature src.K))
      change N.network.denote=NoXWeightedAntiSigned.anti b c
      rw [form]
      funext x
      cases h0 : x 0 <;> cases h1 : x 1 <;>
        simp [binary,NoXWeightedAntiSigned.anti,ha,h0,h1]
    rcases NoXWeightedAntiComplete.tract_or_hard G next (A.newLabel src.H) b c nonzeroB nonzeroC literal with positive|hard
    · exact Or.inl (positive.mono_family (NoXOrdinaryGraphSource.old_included G src (output src.H N)))
    · exact Or.inr hard
  · by_cases hb : b=0
    · by_cases hc : c=0
      · apply of_sign G src N a ha
        rw [form]
        funext x
        cases h0 : x 0 <;> cases h1 : x 1 <;>
          simp [binary,NoXGeneralZSign.signature,hb,hc,h0,h1]
      · apply of_sign G src (sign src.H (equality G src) (pin G src) (transpose src.H N)) (a*c) (mul_ne_zero ha hc)
        exact sign_value src.H (equality G src) (pin G src) (Macro.row_denote _ _ _) (fun v=>Macro.row_denote _ _ _)
          (transpose src.H N) a c b (transpose_value src.H N a b c form)
    · apply of_sign G src (sign src.H (equality G src) (pin G src) N) (a*b) (mul_ne_zero ha hb)
      exact sign_value src.H (equality G src) (pin G src) (Macro.row_denote _ _ _) (fun v=>Macro.row_denote _ _ _)
        N a b c form

theorem of_trace (N : Macro src.H 2)
    (trace : Matrix.trace (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix N.network.denote)=0)
    (determinant : Matrix.det (Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix N.network.denote)≠0) :
    Tract (GenericOrdinarySource.family G src) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  have last : N.network.denote ![true,true]= -N.network.denote ![false,false] := by
    simp [Matrix.trace,Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix] at trace
    linear_combination trace
  have form : N.network.denote=binary (N.network.denote ![false,false])
      (N.network.denote ![false,true]) (N.network.denote ![true,false]) := by
    funext x
    have word : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
    rw [word]
    cases x 0 <;> cases x 1 <;> simp [binary,last]
  apply classified G src N _ _ _ form
  intro zero
  apply determinant
  rw [Holant.Complexity.BinaryInterpolation.det_entries]
  change N.network.denote ![false,false]*N.network.denote ![true,true]-
    N.network.denote ![false,true]*N.network.denote ![true,false]=0
  rw [last]
  linear_combination zero


end Original
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZTrace
end
