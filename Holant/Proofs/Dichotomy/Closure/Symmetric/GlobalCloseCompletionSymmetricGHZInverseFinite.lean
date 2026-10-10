import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZInverse
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZTrace

/-! Positive physical powers close every finite eigenratio. Together with
finite-target interpolation this installs an inverse edge for every actual
ordinary binary with two distinct nonzero characteristic roots. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZInverseFinite
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain OrdinaryNegativeCubicGadgets
namespace I
export GlobalCloseCompletionSymmetricGHZInverse
  (matrix inversePencil inverse_left inverse_right powers outputArity signatures old_literal new_literal controlled)
end I
namespace A
export NoXOrdinaryGraphAdjoin (Output arity signatures source old old_literal newLabel new_literal)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (arity i.val))

def asMacro (N : A.Output H 2) : Macro H 2 := ⟨N.network,N.labels,N.exact,N.ordinary⟩
def series (N Q : Macro H 2) : Macro H 2 :=
  ((N.tensor Q).reindex Holant.Complexity.BinaryInterpolation.Chains.seriesOrder).contract
def power (N : Macro H 2) : ℕ→Macro H 2
  | 0=>N
  | k+1=>series H (power N k) N

theorem series_value (N Q : Macro H 2) (B C : Binary (K:=K))
    (hn : N.network.denote=binarySignature B) (hq : Q.network.denote=binarySignature C) :
    (series H N Q).network.denote=binarySignature (B*C) :=
  OrdinaryTargetInterpolationChain.seriesI_denote N.network Q.network B C hn hq

theorem power_value (N : Macro H 2) (B : Binary (K:=K))
    (form : N.network.denote=binarySignature B) (k : ℕ) :
    (power H N k).network.denote=binarySignature (B^(k+1)) := by
  induction k with
  | zero=>simpa [power] using form
  | succ k ih=>
    rw [power,series_value H _ N _ B ih form]
    exact congrArg binarySignature (pow_succ B (k+1)).symm

def output (N : A.Output H 2) (k : ℕ) : A.Output H 2 :=
  GlobalCloseCompletionSymmetricGHZTrace.output H (power H (asMacro H N) k)

theorem output_value (N : A.Output H 2) (k : ℕ) :
    (output H N k).network.denote=binarySignature ((I.matrix H N)^(k+1)) :=
  power_value H (asMacro H N) (I.matrix H N) (binarySignature_binaryMatrix _).symm k

theorem period_power (B : Binary (K:=K)) (a b : K) (distinct : a≠b) (hb : b≠0)
    (trace : Matrix.trace B=a+b) (determinant : Matrix.det B=a*b)
    (t : ℕ) (period : (a/b)^t=1) : B^t=b^t • (1 : Binary (K:=K)) := by
  rw [I.powers B a b distinct hb trace determinant t,period,one_smul]
  congr 1
  module

theorem period_inverse (B : Binary (K:=K)) (a b : K) (distinct : a≠b) (hb : b≠0)
    (trace : Matrix.trace B=a+b) (determinant : Matrix.det B=a*b)
    (t : ℕ) (positive : 0<t) (period : (a/b)^t=1) :
    B^(2*t-1)*B=b^(2*t) • (1 : Binary (K:=K)) ∧
      B*B^(2*t-1)=b^(2*t) • (1 : Binary (K:=K)) := by
  have p : (a/b)^(2*t)=1 := by rw [mul_comm 2 t,pow_mul,period,one_pow]
  have ht : 2*t-1+1=2*t := by omega
  constructor
  · rw [←pow_succ,ht,period_power B a b distinct hb trace determinant (2*t) p]
  · rw [←pow_succ',ht,period_power B a b distinct hb trace determinant (2*t) p]

section Source
variable [Algebra ℚ K] {degree : ℕ}
variable (field : FixedField K degree) (N : A.Output H 2)

structure Extension where
  count : ℕ
  b : ℕ→ℕ
  table : (i : Fin count)→Signature K (b i.val)
  old : Fin r→Fin count
  old_literal : ∀i,(⟨b (old i).val,table (old i)⟩ : AnySignature K)=⟨arity i.val,H i⟩
  inverse : Binary (K:=K)
  scalar : K
  nonzero : scalar≠0
  label : Fin count
  literal : (⟨b label.val,table label⟩ : AnySignature K)=⟨2,binarySignature inverse⟩
  left_inverse : inverse*I.matrix H N=scalar • (1 : Binary (K:=K))
  right_inverse : I.matrix H N*inverse=scalar • (1 : Binary (K:=K))
  source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) field.encoding
    (RawClosedNetwork.validatedEncoding r 1 arity) field.encoding
    ((QuaternaryOrdinaryCompanion.tables field table).evaluate field)
    ((QuaternaryOrdinaryCompanion.tables field H).evaluate field)

variable (a b : K) (distinct : a≠b) (ha : a≠0) (hb : b≠0)
variable (trace : Matrix.trace (I.matrix H N)=a+b) (determinant : Matrix.det (I.matrix H N)=a*b)

def finite (t : ℕ) (positive : 0<t) (period : (a/b)^t=1) : Extension H field N := by
  let d:=output H N (2*t-2)
  have count : 2*t-2+1=2*t-1 := by omega
  have inverse:=period_inverse (I.matrix H N) a b distinct hb trace determinant t positive period
  exact {
    count:=r+1
    b:=A.arity H d
    table:=A.signatures field H d
    old:=A.old H
    old_literal:=A.old_literal field H d
    inverse:=(I.matrix H N)^(2*t-1)
    scalar:=b^(2*t)
    nonzero:=pow_ne_zero _ hb
    label:=A.newLabel H
    literal:=(A.new_literal field H d).trans (congrArg
      (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K)) (by
        change (output H N (2*t-2)).network.denote=_
        rw [output_value,count]))
    left_inverse:=inverse.1
    right_inverse:=inverse.2
    source:=A.source field H d }

def infinite (period : ∀k : ℕ,0<k→(a/b)^k≠1) : Extension H field N where
  count:=r+1
  b:=I.outputArity field H N a b
  table:=I.signatures field H N a b
  old:=Fin.castAdd 1
  old_literal:=I.old_literal field H N a b
  inverse:=I.inversePencil (I.matrix H N) a b
  scalar:=b
  nonzero:=hb
  label:=⟨r,Nat.lt_succ_self _⟩
  literal:=I.new_literal field H N a b
  left_inverse:=I.inverse_left (I.matrix H N) a b distinct ha trace determinant
  right_inverse:=I.inverse_right (I.matrix H N) a b distinct ha trace determinant
  source:=I.controlled field H N a b distinct ha hb trace determinant period

/-- Periodicity is decided only for the fixed matrix. Both branches return
an implemented source and the same complete old dictionary. -/
def produce : Extension H field N := by
  classical
  by_cases period : ∃t : ℕ,0<t ∧ (a/b)^t=1
  · exact finite H field N a b distinct hb trace determinant period.choose
      period.choose_spec.1 period.choose_spec.2
  · exact infinite H field N a b distinct ha hb trace determinant
      (fun k hk eqn=>period ⟨k,hk,eqn⟩)


end Source
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZInverseFinite
end
