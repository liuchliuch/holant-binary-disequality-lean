import Holant.Certificates.OctahedralSeparator.TensorSemantics
import Holant.Certificates.OctahedralSeparator.TensorData
import Holant.Certificates.TetrahedralOrientation.Data

/-! A proved four-integer coefficient checker. Denominators are cleared before
the finite kernel computation; its results are transported to the actual
Q(sqrt2,i) tensor operations by the evaluation identities below. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000

structure IntegerCoefficient where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

namespace IntegerCoefficient

def add (u v : IntegerCoefficient) : IntegerCoefficient :=
  ⟨u.a+v.a,u.b+v.b,u.c+v.c,u.d+v.d⟩
def mul (u v : IntegerCoefficient) : IntegerCoefficient :=
  ⟨u.a*v.a+2*u.b*v.b-u.c*v.c-2*u.d*v.d,
    u.a*v.b+u.b*v.a-u.c*v.d-u.d*v.c,
    u.a*v.c+2*u.b*v.d+u.c*v.a+2*u.d*v.b,
    u.a*v.d+u.b*v.c+u.c*v.b+u.d*v.a⟩
def eval (u : IntegerCoefficient) : Scalar := coeff u.a u.b u.c u.d

theorem eval_add (u v : IntegerCoefficient) : eval (add u v)=eval u+eval v := by
  apply embed_injective
  simp only [eval,add,embed_coeff,embed_add]
  push_cast
  ring

theorem eval_mul (u v : IntegerCoefficient) : eval (mul u v)=eval u*eval v := by
  apply embed_injective
  simp only [eval,mul,embed_coeff,embed_mul]
  push_cast
  ring_nf
  simp [rootTwo_sq,Complex.I_sq]
  ring

def sumBool (f : Bool → IntegerCoefficient) : IntegerCoefficient := add (f false) (f true)

theorem eval_sumBool (f : Bool → IntegerCoefficient) :
    eval (sumBool f)=∑ a : Bool, eval (f a) := by
  simp [sumBool,eval_add,add_comm]

def action (L : Fin 4 → Bool → Bool → IntegerCoefficient) (t : Word → IntegerCoefficient)
    (x : Word) : IntegerCoefficient :=
  sumBool fun a => sumBool fun b => sumBool fun c => sumBool fun d =>
    mul (mul (mul (mul (L 0 (x 0) a) (L 1 (x 1) b)) (L 2 (x 2) c)) (L 3 (x 3) d))
      (t ![a,b,c,d])

theorem eval_action (L : Fin 4 → Bool → Bool → IntegerCoefficient) (t : Word → IntegerCoefficient) :
    (fun x => eval (action L t x))=
      Signature.coordinateAction (fun j a b => eval (L j a b)) (fun x => eval (t x)) := by
  funext x
  simp only [action,eval_sumBool,eval_mul]
  simp only [Signature.coordinateAction,TetrahedralOrientation.sum_four,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ,Fin.isValue]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Fin.prod_univ_zero,mul_one]
  change eval (L 0 (x 0) a)*eval (L 1 (x 1) b)*eval (L 2 (x 2) c)*eval (L 3 (x 3) d)*eval (t ![a,b,c,d]) =
    (eval (L 0 (x 0) a)*(eval (L 1 (x 1) b)*(eval (L 2 (x 2) c)*eval (L 3 (x 3) d))))*eval (t ![a,b,c,d])
  ring

end IntegerCoefficient

theorem action_scale (c d : Scalar) (L : Fin 4 → Mat) (t : Signature Scalar 4) :
    Signature.coordinateAction (fun j => ms c (L j)) (tensorScale d t)=
      tensorScale (c^4*d) (Signature.coordinateAction L t) := by
  funext x
  simp only [Signature.coordinateAction,ms,tensorScale,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem integer_action_certificate
    (L : Fin 4 → Mat) (t u : Signature Scalar 4) (c d : Scalar)
    (ic : Fin 4 → Bool → Bool → IntegerCoefficient) (it iu : Word → IntegerCoefficient)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hL : ∀ j a b, IntegerCoefficient.eval (ic j a b)=c*L j a b)
    (ht : ∀ x, IntegerCoefficient.eval (it x)=d*t x)
    (hu : ∀ x, IntegerCoefficient.eval (iu x)=c^4*d*u x)
    (hcheck : ∀ x, IntegerCoefficient.action ic it x=iu x) :
    u=Signature.coordinateAction L t := by
  have he := IntegerCoefficient.eval_action ic it
  simp_rw [hcheck,hL,ht] at he
  change (fun x => IntegerCoefficient.eval (iu x))=
    Signature.coordinateAction (fun j => ms c (L j)) (tensorScale d t) at he
  rw [action_scale] at he
  funext x
  have hx := congrFun he x
  rw [hu x] at hx
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 4 hc) hd) hx

end Holant.Certificates.OctahedralSeparator
