import Holant.Tractable.CommonTransform
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.CommRing


namespace Holant.LocalDrafts.MainChain.TransformRecognition.SymbolicTransform
open Holant.Tractable MvPolynomial
noncomputable section

abbrev Variables (τ : Type*) := Fin 5 ⊕ τ
abbrev Poly (τ : Type*) := MvPolynomial (Variables τ) AlgebraicComplex

def index (u v : Bool) : Fin 5 := if u then (if v then 3 else 2) else (if v then 1 else 0)

def matrix {R τ : Type*} (x : Variables τ → R) : Kernel R :=
  fun u v => x (.inl (index u v))

def adjugate {R : Type*} [Neg R] (U : Kernel R) : Kernel R :=
  fun u v => if u=v then U (!u) (!v) else -U u v

def determinant {R : Type*} [Ring R] (U : Kernel R) : R :=
  U false false * U true true - U false true * U true false

def inverse {R τ : Type*} [Ring R] (x : Variables τ → R) : Kernel R :=
  fun u v => x (.inl 4)*adjugate (matrix x) u v

def symbolic (τ : Type*) : Kernel (Poly τ) := matrix (fun v => X v)
def symbolicInverse (τ : Type*) : Kernel (Poly τ) := inverse (fun v => X v)

def guard (τ : Type*) : Poly τ := X (.inl 4)*determinant (symbolic τ)-1

def vertex {τ : Type*} {n : ℕ} (f : Signature AlgebraicComplex n) :
    Signature (Poly τ) n :=
  Signature.coordinateAction (fun _ => symbolicInverse τ) (fun x => C (f x))

def edge {τ : Type*} (E : Kernel AlgebraicComplex) : Kernel (Poly τ) :=
  Kernel.pullback (fun u v => C (E u v)) (symbolic τ)

variable {R τ : Type*} [CommRing R] (φ : AlgebraicComplex →+* R) (x : Variables τ → R)

theorem eval_matrix (u v : Bool) : eval₂ φ x (symbolic τ u v)=matrix x u v := by
  simp [symbolic,matrix]

theorem eval_inverse (u v : Bool) : eval₂ φ x (symbolicInverse τ u v)=inverse x u v := by
  cases u <;> cases v <;> simp [symbolicInverse,inverse,adjugate,matrix,index]

theorem eval_guard : eval₂ φ x (guard τ)=x (.inl 4)*determinant (matrix x)-1 := by
  simp [guard,determinant,eval_matrix]

theorem eval_vertex {n : ℕ} (f : Signature AlgebraicComplex n) (y : Fin n → Bool) :
    eval₂ φ x (vertex (τ:=τ) f y)=
      Signature.coordinateAction (fun _ => inverse x) (fun z => φ (f z)) y := by
  simp [vertex,Signature.coordinateAction,eval_inverse]

theorem eval_edge (E : Kernel AlgebraicComplex) (u v : Bool) :
    eval₂ φ x (edge (τ:=τ) E u v)=
      Kernel.pullback (fun a b => φ (E a b)) (matrix x) u v := by
  simp [edge,Kernel.pullback,Kernel.mul,Kernel.transpose,eval_matrix]

/-- The single guard supplies both inverse identities over every target
commutative ring; there is no division operation in the compiled entries. -/
theorem inverse_identities (h : eval₂ φ x (guard τ)=0) :
    Kernel.mul (matrix x) (inverse x)=Signature.equality ∧
      Kernel.mul (inverse x) (matrix x)=Signature.equality := by
  have hg : x (.inl 4)*determinant (matrix x)=1 := by
    apply sub_eq_zero.mp
    rwa [eval_guard] at h
  have he : x (.inl 4)*(x (.inl 0)*x (.inl 3)-x (.inl 1)*x (.inl 2))=1 := hg
  constructor <;> funext u v <;> cases u <;> cases v <;>
    simp [Kernel.mul,matrix,inverse,adjugate,index,Signature.equality]
  all_goals first | (solve | ring) | linear_combination he

/-- Specializing a branch solution gives the actual two-sided inverse
object used by the source transformability predicate. -/
def toInvertible (x : Variables τ → AlgebraicComplex)
    (h : eval₂ (RingHom.id AlgebraicComplex) x (guard τ)=0) : InvertibleKernel where
  matrix := matrix x
  inverse := inverse x
  matrix_inverse := (inverse_identities (RingHom.id AlgebraicComplex) x h).1
  inverse_matrix := (inverse_identities (RingHom.id AlgebraicComplex) x h).2

theorem selected_vertex (x : Variables τ → AlgebraicComplex)
    (h : eval₂ (RingHom.id AlgebraicComplex) x (guard τ)=0)
    {n : ℕ} (f : Signature AlgebraicComplex n) (y : Fin n → Bool) :
    eval₂ (RingHom.id AlgebraicComplex) x (vertex (τ:=τ) f y)=
      Signature.coordinateAction (fun _ => (toInvertible x h).inverse) f y :=
  eval_vertex (RingHom.id AlgebraicComplex) x f y

theorem selected_edge (x : Variables τ → AlgebraicComplex)
    (h : eval₂ (RingHom.id AlgebraicComplex) x (guard τ)=0)
    (E : Kernel AlgebraicComplex) (u v : Bool) :
    eval₂ (RingHom.id AlgebraicComplex) x (edge (τ:=τ) E u v)=
      Kernel.pullback E (toInvertible x h).matrix u v :=
  eval_edge (RingHom.id AlgebraicComplex) x E u v

theorem determinant_mul (U V : Kernel R) :
    determinant (Kernel.mul U V)=determinant U*determinant V := by
  simp [determinant,Kernel.mul]
  ring

theorem determinant_nonzero_of_inverse (U V : Kernel R)
    [Nontrivial R] (hUV : Kernel.mul U V=Signature.equality) : determinant U ≠ 0 := by
  have hd := congrArg determinant hUV
  rw [determinant_mul] at hd
  have he : determinant (Signature.equality : Kernel R)=1 := by
    simp [determinant,Signature.equality]
  rw [he] at hd
  intro hz
  simp [hz] at hd

section Field
variable {E : Type*} [Field E] (ψ : AlgebraicComplex →+* E)

def point (U : Kernel E) (parameters : τ → E) : Variables τ → E :=
  Sum.elim (fun i => ![U false false,U false true,U true false,U true true,(determinant U)⁻¹] i)
    parameters

theorem point_matrix (U : Kernel E) (parameters : τ → E) : matrix (point U parameters)=U := by
  funext u v
  cases u <;> cases v <;> rfl

theorem point_guard (U V : Kernel E) (parameters : τ → E)
    (hUV : Kernel.mul U V=Signature.equality) :
    eval₂ ψ (point U parameters) (guard τ)=0 := by
  rw [eval_guard,point_matrix]
  change (determinant U)⁻¹*determinant U-1=0
  rw [inv_mul_cancel₀ (determinant_nonzero_of_inverse U V hUV),sub_self]

include ψ in
theorem point_inverse (U V : Kernel E) (parameters : τ → E)
    (hUV : Kernel.mul U V=Signature.equality)
    (hVU : Kernel.mul V U=Signature.equality) : inverse (point U parameters)=V := by
  have hi := (inverse_identities ψ (point U parameters) (point_guard ψ U V parameters hUV)).1
  rw [point_matrix] at hi
  calc
    inverse (point U parameters)=Kernel.mul Signature.equality (inverse (point U parameters)) :=
      (Kernel.equality_mul _).symm
    _=Kernel.mul (Kernel.mul V U) (inverse (point U parameters)) := by rw [hVU]
    _=Kernel.mul V (Kernel.mul U (inverse (point U parameters))) := Kernel.mul_assoc _ _ _
    _=V := by rw [hi,Kernel.mul_equality]

/-- An existing source inverse witness satisfies the polynomial guard and
all compiled entries evaluate to the same actual transformed tensors. This
is the reverse bridge needed before applying algebraic point descent. -/
theorem point_vertex (U V : Kernel E) (parameters : τ → E)
    (hUV : Kernel.mul U V=Signature.equality)
    (hVU : Kernel.mul V U=Signature.equality)
    {n : ℕ} (f : Signature AlgebraicComplex n) (y : Fin n → Bool) :
    eval₂ ψ (point U parameters) (vertex (τ:=τ) f y)=
      Signature.coordinateAction (fun _ => V) (fun z => ψ (f z)) y := by
  rw [eval_vertex,point_inverse ψ U V parameters hUV hVU]

theorem point_edge (U : Kernel E) (parameters : τ → E)
    (E₀ : Kernel AlgebraicComplex) (u v : Bool) :
    eval₂ ψ (point U parameters) (edge (τ:=τ) E₀ u v)=
      Kernel.pullback (fun a b => ψ (E₀ a b)) U u v := by
  rw [eval_edge,point_matrix]

end Field

end
end Holant.LocalDrafts.MainChain.TransformRecognition.SymbolicTransform
