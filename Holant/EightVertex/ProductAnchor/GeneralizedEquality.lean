import Holant.EightVertex.ProductAnchor.MatrixForms
import Holant.Tractable.Conformal.MatrixSupport

namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

abbrev Word4 := Fin 4 → Bool

@[simp] theorem complement_zero_four : Tractable.complementWord (fun _ : Fin 4 => false)=(fun _ => true) := rfl
@[simp] theorem complement_one_four : Tractable.complementWord (fun _ : Fin 4 => true)=(fun _ => false) := rfl
@[simp] theorem zero_ne_one_four : (fun _ : Fin 4 => false)≠(fun _ => true) := by decide
@[simp] theorem one_ne_zero_four : (fun _ : Fin 4 => true)≠(fun _ => false) := by decide

def ge4 (A B : Scalar) (s : Word4) : Signature Scalar 4 := fun x =>
  (if x=s then A else 0)+(if x=complementWord s then B else 0)

def bitSign (s x : Word4) : Scalar := (-1)^(∑ i : Fin 4,if s i && x i then 1 else 0 : ℕ)

def EndpointEven (q : Signature Scalar 4) : Prop :=
  q (fun _ => false)≠0 ∧ q (fun _ => true)≠0 ∧
    ∀ x,Holant.weight x % 2=1 → q x=0

def DenseForm (q : Signature Scalar 4) : Prop :=
  ∃ rho r : Scalar,rho≠0 ∧ r≠0 ∧ ∃ s : Word4,∀ x,
    q x=if Holant.weight x % 2=0 then rho*r^(Holant.weight x)*bitSign s x else 0

def PureEquality (q : Signature Scalar 4) : Prop :=
  ∃ A B : Scalar,A≠0 ∧ B≠0 ∧ q=ge4 A B (fun _ => false)

theorem word_ne_complement (s : Word4) : s≠complementWord s := by
  intro h
  have H := congrFun h 0
  cases hs : s 0 <;> simp [complementWord,hs] at H

@[simp] theorem ge4_left (A B : Scalar) (s : Word4) : ge4 A B s s=A := by
  simp [ge4,word_ne_complement]

@[simp] theorem ge4_right (A B : Scalar) (s : Word4) : ge4 A B s (complementWord s)=B := by
  simp [ge4,Ne.symm (word_ne_complement s)]

theorem ge4_outside (A B : Scalar) (s x : Word4) (hx : x≠s) (hy : x≠complementWord s) :
    ge4 A B s x=0 := by simp [ge4,hx,hy]

theorem of_complement_support (q : Signature Scalar 4) (s : Word4)
    (h : ∀ x,x≠s → x≠complementWord s → q x=0) :
    q=ge4 (q s) (q (complementWord s)) s := by
  funext x
  by_cases hx : x=s
  · subst x; simp
  by_cases hy : x=complementWord s
  · subst x; simp
  simp [ge4,hx,hy,h x hx hy]

theorem action_ge4 (T : Mat) (A B : Scalar) (s x : Word4) :
    Signature.coordinateAction (fun _ => T) (ge4 A B s) x=
      A*(∏ i,T (x i) (s i))+B*(∏ i,T (x i) (complementWord s i)) := by
  simp [Signature.coordinateAction,ge4,mul_add,Finset.sum_add_distrib,mul_comm]

theorem bitSign_ne_zero (s x : Word4) : bitSign s x≠0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

theorem balanced_product (a c r : Scalar) (s x : Word4) :
    (∏ i,balanced a c r (x i) (s i))=
      a^(4-Holant.weight x)*c^(Holant.weight x)*r^(Holant.weight s)*bitSign s x := by
  have H (i : Fin 4) : balanced a c r (x i) (s i)=
      (if x i then c else a)*(if s i then r else 1)*
        (-1)^(if s i && x i then 1 else 0 : ℕ) := by
    cases hx : x i <;> cases hs : s i <;> simp [balanced,matrix,hx,hs] <;> ring
  simp_rw [H]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  change diagonalCoefficient a c x*diagonalCoefficient 1 r s*
      (∏ i : Fin 4,(-1:Scalar)^(if s i && x i then 1 else 0 : ℕ))=_
  rw [diagonalCoefficient_eq_weight,diagonalCoefficient_eq_weight,Finset.prod_pow_eq_pow_sum]
  simp [bitSign]

theorem bitSign_complement (s x : Word4) :
    bitSign (complementWord s) x=bitSign s x*(-1)^(Holant.weight x) := by
  let d : ℕ := ∑ i : Fin 4,if s i && x i then 1 else 0
  let e : ℕ := ∑ i : Fin 4,if !(s i) && x i then 1 else 0
  have he : e+d=Holant.weight x := by
    dsimp [d,e,Holant.weight]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases s i <;> cases x i <;> rfl
  have hu : (-1:Scalar)^d*(-1:Scalar)^d=1 := by rw [←mul_pow]; simp
  change (-1:Scalar)^e=(-1:Scalar)^d*(-1:Scalar)^(Holant.weight x)
  calc
    _ = ((-1:Scalar)^e*(-1:Scalar)^d)*(-1:Scalar)^d := by rw [mul_assoc,hu,mul_one]
    _ = (-1:Scalar)^(Holant.weight x)*(-1:Scalar)^d := by rw [←pow_add,he]
    _ = _ := mul_comm _ _

theorem action_balanced_ge4 (a c r A B : Scalar) (s x : Word4) :
    Signature.coordinateAction (fun _ => balanced a c r) (ge4 A B s) x=
      a^(4-Holant.weight x)*c^(Holant.weight x)*bitSign s x*
        (A*r^(Holant.weight s)+B*r^(4-Holant.weight s)*(-1)^(Holant.weight x)) := by
  have hw : Holant.weight (complementWord s)=4-Holant.weight s := by
    have H := Holant.weight_compl_add s
    change Holant.weight (complementWord s)+Holant.weight s=4 at H
    omega
  rw [action_ge4,balanced_product,balanced_product,bitSign_complement,hw]
  ring

theorem row_weight_ratio (a c : Scalar) (ha : a≠0) (x : Word4) :
    a^(4-Holant.weight x)*c^(Holant.weight x)=a^4*(c/a)^(Holant.weight x) := by
  have hn := Holant.weight_le x
  have hp : a^4=a^(4-Holant.weight x)*a^(Holant.weight x) := by
    rw [←pow_add,Nat.sub_add_cancel hn]
  rw [div_pow,hp]
  field_simp [pow_ne_zero (Holant.weight x) ha]

end
end Holant.EightVertex.ProductAnchor
