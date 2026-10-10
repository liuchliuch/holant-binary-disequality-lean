import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZInverseFinite
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZRegularCap
import Holant.Complexity.BinaryInterpolation.RepeatedRoot

/-! Real unary walks and real unary caps of a symmetric ternary. Repeated
characteristic-root powers retain their exact nonzero scale and the actual
old labels; the five-sample selector does not ask for arbitrary free unaries. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCapGraph
open Holant Holant.Tractable Holant.Complexity
open Holant.Certificates.MatchingContractionClosure
open Holant.Complexity.BinaryInterpolation
open Holant.LocalDrafts.MainChain
open OrdinaryNegativeCubicGadgets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def symmetric (a b c d : K) : Signature K 3 := fun x=>
  if x 0 then (if x 1 then (if x 2 then d else c) else (if x 2 then c else b))
  else if x 1 then (if x 2 then c else b) else (if x 2 then b else a)

def pencil (a b c d p q : K) : Binary (K:=K) := fun i j=>
  if i then (if j then p*c+q*d else p*b+q*c)
  else if j then p*b+q*c else p*a+q*b

theorem pencil_det (a b c d p q : K) :
    Matrix.det (pencil a b c d p q)=(p*a+q*b)*(p*c+q*d)-(p*b+q*c)^2 := by
  rw [det_entries]
  simp [pencil,pow_two]
theorem pencil_trace (a b c d p q : K) :
    Matrix.trace (pencil a b c d p q)=p*(a+c)+q*(b+d) := by
  simp [pencil,Matrix.trace]
  ring

variable {r : ℕ} {arity : ℕ→ℕ}
variable {H : (i : Fin r)→Signature K (arity i.val)}

def cap (N : Macro H 3) (U : Macro H 1) : Macro H 2 := (U.tensor N).contract
def step (Q : Macro H 2) (U : Macro H 1) : Macro H 1 := (U.tensor Q).contract
def walk (Q : Macro H 2) (P : Macro H 1) : ℕ→Macro H 1
  | 0=>P
  | k+1=>step Q (walk Q P k)

theorem cap_value (N : Macro H 3) (U : Macro H 1) (x : Fin 2→Bool) :
    (cap N U).network.denote x=U.network.denote (fun _=>false)*N.network.denote ![false,x 0,x 1]+
      U.network.denote (fun _=>true)*N.network.denote ![true,x 0,x 1] := by
  rw [cap,Macro.contract_denote,Macro.tensor_denote]
  simp only [Signature.tensor_apply]
  have un (v : Bool) : (fun i : Fin 1=>(Fin.cons v (Fin.cons v x) : Fin 4→Bool) (Fin.castAdd 3 i))=(fun _=>v) := by
    funext i; fin_cases i; rfl
  have tr (v : Bool) : (fun i : Fin 3=>(Fin.cons v (Fin.cons v x) : Fin 4→Bool) (Fin.natAdd 1 i))=![v,x 0,x 1] := by
    funext i; fin_cases i <;> rfl
  simp only [un,tr]

theorem cap_form (N : Macro H 3) (U : Macro H 1) (a b c d p q : K)
    (form : N.network.denote=symmetric a b c d)
    (first : U.network.denote (fun _=>false)=p) (second : U.network.denote (fun _=>true)=q) :
    (cap N U).network.denote=binarySignature (pencil a b c d p q) := by
  funext x
  rw [cap_value,first,second,form]
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [symmetric,pencil,binarySignature,h0,h1]

theorem cap_scaled (N : Macro H 3) (U : Macro H 1) (a b c d p q z : K)
    (form : N.network.denote=symmetric a b c d)
    (first : U.network.denote (fun _=>false)=z*p) (second : U.network.denote (fun _=>true)=z*q) :
    (cap N U).network.denote=binarySignature (z • pencil a b c d p q) := by
  rw [cap_form N U a b c d (z*p) (z*q) form first second]
  apply congrArg binarySignature
  ext i j
  cases i <;> cases j <;> simp [pencil,Matrix.smul_apply,smul_eq_mul] <;> ring

theorem walk_value (Q : Macro H 2) (P : Macro H 1) (B : Binary (K:=K))
    (form : Q.network.denote=binarySignature B) (pin : P.network.denote=QuaternaryUnaryAccess.pin false)
    (k : ℕ) : (walk Q P k).network.denote=fun x=>(B^k) false (x 0) := by
  induction k with
  | zero=>
    rw [walk,pin]
    funext x
    cases h : x 0 <;> simp [QuaternaryUnaryAccess.pin,h,Matrix.one_apply]
  | succ k ih=>
    rw [walk,step]
    funext x
    rw [Macro.contract_denote,Macro.tensor_denote,ih,form,pow_succ]
    simp [Signature.tensor_apply,binarySignature,Matrix.mul_apply,Fintype.sum_bool,add_comm]

variable [CharZero K]

theorem walk_jordan (Q : Macro H 2) (P : Macro H 1) (B : Binary (K:=K))
    (form : Q.network.denote=binarySignature B) (pin : P.network.denote=QuaternaryUnaryAccess.pin false)
    (mu : K) (nonzero : mu≠0) (trace : Matrix.trace B=mu+mu) (determinant : Matrix.det B=mu*mu)
    (k : ℕ) : (walk Q P k).network.denote=fun x=>mu^k*
      (if x 0 then (k:K)*(B false true/mu) else 1+(k:K)*((B false false-mu)/mu)) := by
  rw [walk_value Q P B form pin k,repeated_power B mu nonzero trace determinant]
  funext x
  cases h : x 0 <;>
    simp [Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.one_apply,nilpotentPart,h,smul_eq_mul,div_eq_mul_inv]
  all_goals ring_nf <;> simp

theorem cap_jordan (N : Macro H 3) (Q : Macro H 2) (P : Macro H 1)
    (a b c d : K) (form : N.network.denote=symmetric a b c d)
    (B : Binary (K:=K)) (binary : Q.network.denote=binarySignature B)
    (pin : P.network.denote=QuaternaryUnaryAccess.pin false)
    (mu : K) (nonzero : mu≠0) (trace : Matrix.trace B=mu+mu) (determinant : Matrix.det B=mu*mu)
    (k : ℕ) : (cap N (walk Q P k)).network.denote=binarySignature
      (mu^k • pencil a b c d (1+(k:K)*((B false false-mu)/mu)) ((k:K)*(B false true/mu))) := by
  apply cap_scaled N (walk Q P k) a b c d _ _ (mu^k) form
  · rw [walk_jordan Q P B binary pin mu nonzero trace determinant]; rfl
  · rw [walk_jordan Q P B binary pin mu nonzero trace determinant]; rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZCapGraph
end
