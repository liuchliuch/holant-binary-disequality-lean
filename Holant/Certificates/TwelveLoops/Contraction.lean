import Holant.Certificates.TwelveLoops.Data
import Holant.Tensor

/-! The twelve pairs are the coefficients of literal physical contractions
of the odd quaternary table, with original local-port and residual-port order. -/
namespace Holant.Certificates.TwelveLoops
open Holant

def portOrder : Fin 6 → Fin 4 → Fin 4 :=
  ![![0,1,2,3],![0,2,1,3],![0,3,1,2],![1,2,0,3],![1,3,0,2],![2,3,0,1]]
def portInverse : Fin 6 → Fin 4 → Fin 4 :=
  ![![0,1,2,3],![0,2,1,3],![0,2,3,1],![2,0,1,3],![2,0,3,1],![2,3,0,1]]

def portEquiv (p : Fin 6) : Equiv.Perm (Fin 4) where
  toFun := portOrder p
  invFun := portInverse p
  left_inv := by
    have h : ∀ p i, portInverse p (portOrder p i)=i := by decide
    exact h p
  right_inv := by
    have h : ∀ p i, portOrder p (portInverse p i)=i := by decide
    exact h p

theorem portOrder_selected : ∀ p : Fin 6,
    portOrder p 0=(pairs p).1 ∧ portOrder p 1=(pairs p).2 ∧
    portOrder p 2=(complements p).1 ∧ portOrder p 3=(complements p).2 := by decide

variable {K : Type*} [Semiring K]

def oddTable (a b : Fin 4 → K) : Signature K 4 := fun x =>
  match x 0,x 1,x 2,x 3 with
  | true,false,false,false => a 0
  | false,true,false,false => a 1
  | false,false,true,false => a 2
  | false,false,false,true => a 3
  | false,true,true,true => b 0
  | true,false,true,true => b 1
  | true,true,false,true => b 2
  | true,true,true,false => b 3
  | _,_,_,_ => 0

def singleWord (j : Fin 4) : Fin 4 → Bool := fun i => decide (i=j)
def complementWord (j : Fin 4) : Fin 4 → Bool := fun i => decide (i≠j)

theorem oddTable_single (a b : Fin 4 → K) (j : Fin 4) :
    oddTable a b (singleWord j)=a j := by fin_cases j <;> simp [oddTable,singleWord]
theorem oddTable_complement (a b : Fin 4 → K) (j : Fin 4) :
    oddTable a b (complementWord j)=b j := by fin_cases j <;> simp [oddTable,complementWord]

def loopAt (a b : Fin 4 → K) (p : Fin 6) (native : Bool) : Signature K 2 :=
  Signature.contract (if native then Signature.disequality else Signature.equality)
    (Tensor.reindex (portEquiv p).symm (oddTable a b))

def diagonal (P Q : K) : Signature K 2 := fun x => if x 0=x 1 then if x 0 then Q else P else 0
def antidiagonal (P Q : K) : Signature K 2 := fun x => if x 0≠x 1 then if x 0 then Q else P else 0

@[simp] theorem cons_cons_two (c d : Bool) (x : Fin 2 → Bool) :
    (Fin.cons (α := fun _ : Fin 4 => Bool) c (Fin.cons d x)) 2=x 0 := rfl
@[simp] theorem cons_cons_three (c d : Bool) (x : Fin 2 → Bool) :
    (Fin.cons (α := fun _ : Fin 4 => Bool) c (Fin.cons d x)) 3=x 1 := rfl

theorem native_loop_formula (a b : Fin 4 → K) (p : Fin 6) :
    loopAt a b p true = diagonal (a (pairs p).1+a (pairs p).2) (b (pairs p).1+b (pairs p).2) := by
  funext x
  fin_cases p <;> cases h₀ : x 0 <;> cases h₁ : x 1 <;>
    simp [loopAt,Signature.contract_disequality,Tensor.reindex,portEquiv,portInverse,
      oddTable,diagonal,pairs,h₀,h₁,add_comm]

theorem equality_loop_formula (a b : Fin 4 → K) (p : Fin 6) :
    loopAt a b p false = antidiagonal
      (a (complements p).2+b (complements p).1) (a (complements p).1+b (complements p).2) := by
  funext x
  fin_cases p <;> cases h₀ : x 0 <;> cases h₁ : x 1 <;>
    simp [loopAt,Signature.contract_equality,Tensor.reindex,portEquiv,portInverse,
      oddTable,antidiagonal,complements,h₀,h₁,add_comm]

/-- The literal two native-X edges and one equality vertex. The four summed
bits are the two original tensor ends and the two equality-vertex ends. -/
def equalityMediatedLoop (a b : Fin 4 → K) (p : Fin 6) : Signature K 2 := fun x =>
  ∑ u : Bool, ∑ v : Bool, ∑ r : Bool, ∑ t : Bool,
    Signature.disequality u r * Signature.equality r t * Signature.disequality v t *
      Tensor.reindex (portEquiv p).symm (oddTable a b) (Fin.cons u (Fin.cons v x))

theorem equality_mediated_eq (a b : Fin 4 → K) (p : Fin 6) :
    equalityMediatedLoop a b p=loopAt a b p false := by
  funext x
  simp [equalityMediatedLoop,loopAt,Signature.contract_equality,
    Signature.disequality,Signature.equality,add_comm]

theorem equality_mediated_formula (a b : Fin 4 → K) (p : Fin 6) :
    equalityMediatedLoop a b p=antidiagonal
      (a (complements p).2+b (complements p).1) (a (complements p).1+b (complements p).2) := by
  rw [equality_mediated_eq,equality_loop_formula]

end Holant.Certificates.TwelveLoops
