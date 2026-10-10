import Holant.Certificates.EqualityQuaternary.MonomialSource
import Holant.Algebraic.QuadraticField
import Mathlib.Logic.Equiv.Fintype

/-! Literal algebraic Pauli/exotic bases and Frobenius duals, with an exact
Gaussian-rational evaluation map for the upcoming finite certificates. -/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein
open Holant Holant.Marked Holant.Tractable
set_option backward.isDefEq.respectTransparency false

abbrev Q := Algebraic.GaussianRational

def embed : Q →+* Scalar :=
  (QuadraticAlgebra.lift
    (show {u : Scalar // u*u=(-1 : ℚ) • (1 : Scalar)+(0 : ℚ) • u} from
      ⟨imaginaryUnit,by simp [Algebra.smul_def,←pow_two]⟩)).toRingHom

theorem embed_apply (z : Q) : embed z=(z.re : Scalar)+(z.im : Scalar)*imaginaryUnit := by
  simp [embed,QuadraticAlgebra.lift,Algebra.smul_def]

inductive Kind | standard | exotic deriving DecidableEq, Fintype

def qI : Q := ⟨0,1⟩
def qHalf : Q := ⟨1/2,0⟩
def qQuarter : Q := ⟨1/4,0⟩
def matrix {K : Type*} (a b c d : K) : Kernel K :=
  fun x y => if x then (if y then d else c) else (if y then b else a)

def basisQ (kind : Kind) (k : Fin 4) : Kernel Q :=
  if k=0 then matrix 1 0 0 1 else if k=1 then matrix 0 1 1 0
  else match kind with
    | .standard => if k=2 then matrix 1 0 0 (-1) else matrix 0 1 (-1) 0
    | .exotic => if k=2 then matrix qI 1 (-1) (-qI) else matrix (-qI) 1 (-1) qI

def dualQ (kind : Kind) (k : Fin 4) : Kernel Q :=
  if k=0 then matrix qHalf 0 0 qHalf else if k=1 then matrix 0 qHalf qHalf 0
  else match kind with
    | .standard => if k=2 then matrix qHalf 0 0 (-qHalf) else matrix 0 qHalf (-qHalf) 0
    | .exotic => if k=2 then matrix (-qQuarter*qI) qQuarter (-qQuarter) (qQuarter*qI)
      else matrix (qQuarter*qI) qQuarter (-qQuarter) (-qQuarter*qI)

def E (kind : Kind) (k : Fin 4) : Mat := fun a b => embed (basisQ kind k a b)
def dual (kind : Kind) (k : Fin 4) : Mat := fun a b => embed (dualQ kind k a b)

theorem dual_pair_Q : ∀ kind a b,
    Kernel.pair (dualQ kind a) (basisQ kind b)=(if a=b then (1:Q) else 0) := by
  intro kind a b
  cases kind <;> fin_cases a <;> fin_cases b <;> decide +kernel

theorem dual_pair (kind : Kind) (a b : Fin 4) :
    Kernel.pair (dual kind a) (E kind b)=(if a=b then (1:Scalar) else 0) := by
  have h := congrArg embed (dual_pair_Q kind a b)
  simpa [Kernel.pair,E,dual] using h

theorem binary_complete_Q : ∀ kind (x y u v : Bool),
    (∑ k : Fin 4,basisQ kind k x y*dualQ kind k u v)=
      (if x=u ∧ y=v then (1:Q) else 0) := by
  intro kind x y u v
  cases kind <;> cases x <;> cases y <;> cases u <;> cases v <;> decide +kernel

theorem binary_complete (kind : Kind) (x y u v : Bool) :
    (∑ k : Fin 4,E kind k x y*dual kind k u v)=
      (if x=u ∧ y=v then (1:Scalar) else 0) := by
  have h := congrArg embed (binary_complete_Q kind x y u v)
  simpa [E,dual] using h

def coefficient (kind : Kind) (B : Mat) (k : Fin 4) : Scalar := Kernel.pair (dual kind k) B

theorem reconstruct_binary (kind : Kind) (B : Mat) (x y : Bool) :
    (∑ k : Fin 4,coefficient kind B k*E kind k x y)=B x y := by
  simp only [coefficient,Kernel.pair,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    intro u
    rw [Finset.sum_comm]
  have hterm (u v : Bool) : (∑ k : Fin 4,dual kind k u v*B u v*E kind k x y)=
      B u v*(if x=u ∧ y=v then 1 else 0) := by
    rw [←binary_complete]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hterm]
  cases x <;> cases y <;> simp

def firstCard (kind : Kind) (q : Signature Scalar 4) (a : Fin 4) : Mat :=
  fun u v => ∑ x : Bool,∑ y : Bool,dual kind a x y*q ![x,y,u,v]
def tensorCoeff (kind : Kind) (q : Signature Scalar 4) (a b : Fin 4) : Scalar :=
  coefficient kind (firstCard kind q a) b
def basisTensor (kind : Kind) (a b : Fin 4) : Signature Scalar 4 :=
  fun w => E kind a (w 0) (w 1)*E kind b (w 2) (w 3)

theorem reconstruct_tensor (kind : Kind) (q : Signature Scalar 4) (w : Fin 4 → Bool) :
    (∑ a : Fin 4,∑ b : Fin 4,tensorCoeff kind q a b*basisTensor kind a b w)=q w := by
  change (∑ a,∑ b,coefficient kind (firstCard kind q a) b*
    (E kind a (w 0) (w 1)*E kind b (w 2) (w 3)))=_
  calc
    _ = ∑ a : Fin 4,E kind a (w 0) (w 1)*
        (∑ b : Fin 4,coefficient kind (firstCard kind q a) b*E kind b (w 2) (w 3)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a : Fin 4,E kind a (w 0) (w 1)*firstCard kind q a (w 2) (w 3) := by
      simp_rw [reconstruct_binary]
    _ = ∑ a : Fin 4,coefficient kind (fun u v => q ![u,v,w 2,w 3]) a*E kind a (w 0) (w 1) := by
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _
    _ = q ![w 0,w 1,w 2,w 3] := reconstruct_binary kind _ (w 0) (w 1)
    _ = q w := by congr 1; funext i; fin_cases i <;> rfl

def OnLine (kind : Kind) (B : Mat) : Prop := ∃ k c,B=scale c (E kind k)

theorem coefficient_line (kind : Kind) (k : Fin 4) (c : Scalar) (i : Fin 4) :
    coefficient kind (scale c (E kind k)) i=if i=k then c else 0 := by
  have h : coefficient kind (scale c (E kind k)) i=c*Kernel.pair (dual kind i) (E kind k) := by
    simp [coefficient,Kernel.pair,scale]
    ring
  rw [h,dual_pair]
  split_ifs <;> simp

theorem onLine_coefficients {kind : Kind} {B : Mat} (h : OnLine kind B) :
    ∃ k,∀ i,i≠k → coefficient kind B i=0 := by
  obtain ⟨k,c,rfl⟩ := h
  exact ⟨k,fun i hi => by simp [coefficient_line,hi]⟩

end Holant.Certificates.EqualityQuaternary.Klein
