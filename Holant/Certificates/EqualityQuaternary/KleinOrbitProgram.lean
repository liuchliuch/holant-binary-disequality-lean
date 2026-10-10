import Holant.Certificates.EqualityQuaternary.KleinPhysicalDeck
import Holant.Certificates.EqualityQuaternary.BoundaryNetwork

/-! Literal exotic local dressings and adjacent port swaps. Analytic actions
are linked to actual representative attachments with every scalar recorded.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein.Orbit
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicDressing
open Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

inductive Op | dress (port : Fin 4) (label : Fin 4) | swap (port : Fin 3)
  deriving DecidableEq

def swapPorts (i : Fin 3) : Equiv.Perm (Fin 4) := Equiv.swap i.castSucc i.succ

def site {K : Type*} [CommSemiring K] (M : Kernel K) (i : Fin 4) (q : Signature K 4) : Signature K 4 :=
  fun w => ∑ b : Bool,M (w i) b*q (Function.update w i b)

def act {K : Type*} [CommSemiring K] (basis : Fin 4 → Kernel K) : Op → Signature K 4 → Signature K 4
  | .dress i j,q => site (basis j) i q
  | .swap i,q => Tensor.reindex (swapPorts i) q

def run {K : Type*} [CommSemiring K] (basis : Fin 4 → Kernel K) : List Op → Signature K 4 → Signature K 4
  | [],q => q
  | op::ops,q => run basis ops (act basis op q)

theorem site_coordinate (M : Mat) (i : Fin 4) (q : Signature Scalar 4) :
    site M i q=Signature.coordinateAction (fun j => if j=i then M else Signature.equality) q := by
  funext w
  fin_cases i <;> cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [site,Signature.coordinateAction,Holant.Projective.CyclicQuaternary.Physical.sum_words4,
      Fin.prod_univ_succ,Signature.equality,update_word4,h0,h1,h2,h3]

theorem act_combination {K : Type*} [CommSemiring K] (basis : Fin 4 → Kernel K)
    (op : Op) (c : Fin 4 → K) (q : Fin 4 → Signature K 4) :
    act basis op (fun w => ∑ r : Fin 4,c r*q r w)=
      fun w => ∑ r : Fin 4,c r*act basis op (q r) w := by
  cases op with
  | swap i => rfl
  | dress i j =>
    funext w
    simp only [act,site,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro b _
    ring

theorem run_combination {K : Type*} [CommSemiring K] (basis : Fin 4 → Kernel K)
    (ops : List Op) (c : Fin 4 → K) (q : Fin 4 → Signature K 4) :
    run basis ops (fun w => ∑ r : Fin 4,c r*q r w)=
      fun w => ∑ r : Fin 4,c r*run basis ops (q r) w := by
  induction ops generalizing q with
  | nil => rfl
  | cons op ops ih => rw [run,act_combination,ih]; rfl

theorem act_smul (basis : Fin 4 → Mat) (op : Op) (c : Scalar) (q : Signature Scalar 4) :
    act basis op (c • q)=c • act basis op q := by
  cases op with
  | swap i => rfl
  | dress i j => funext w; simp [act,site,Finset.mul_sum]; ring

theorem run_smul (basis : Fin 4 → Mat) (ops : List Op) (c : Scalar) (q : Signature Scalar 4) :
    run basis ops (c • q)=c • run basis ops q := by
  induction ops generalizing q with
  | nil => rfl
  | cons op ops ih => rw [run,act_smul,ih]; rfl

theorem act_embed (op : Op) (q : Signature Q 4) :
    (fun w => embed (act (basisQ .exotic) op q w))=
      act (E .exotic) op (fun w => embed (q w)) := by
  cases op <;> funext w <;> simp [act,site,Tensor.reindex,E]

theorem run_embed (ops : List Op) (q : Signature Q 4) :
    (fun w => embed (run (basisQ .exotic) ops q w))=
      run (E .exotic) ops (fun w => embed (q w)) := by
  induction ops generalizing q with
  | nil => rfl
  | cons op ops ih => rw [run,ih,act_embed]; rfl

def invScaleQ (j : Fin 4) : Q := if j=0 ∨ j=1 then 1 else -qHalf
def inverseQ (j : Fin 4) : Kernel Q := fun a b => invScaleQ j*basisQ .exotic j a b
def inverse (j : Fin 4) : Mat := fun a b => embed (inverseQ j a b)

theorem inverse_Q : ∀ j a b,
    Kernel.mul (inverseQ j) (basisQ .exotic j) a b=Signature.equality a b := by
  intro j a b
  fin_cases j <;> cases a <;> cases b <;> decide +kernel

theorem inverse_matrix (j : Fin 4) : Kernel.mul (inverse j) (E .exotic j)=Signature.equality := by
  funext a b
  have h := congrArg embed (inverse_Q j a b)
  cases a <;> cases b <;> simpa [Kernel.mul,inverse,E,Signature.equality] using h

theorem act_prime {q : Signature Scalar 4} (h : TensorPrime q) (op : Op) :
    TensorPrime (act (E .exotic) op q) := by
  cases op with
  | swap i => exact C2.prime_reindex h _
  | dress i j =>
    rw [act,site_coordinate]
    apply prime_coordinateAction h _ (fun k => if k=i then inverse j else Signature.equality)
    intro k
    by_cases hk : k=i <;> simp [hk,inverse_matrix]

theorem run_prime {q : Signature Scalar 4} (h : TensorPrime q) (ops : List Op) :
    TensorPrime (run (E .exotic) ops q) := by
  induction ops generalizing q with
  | nil => exact h
  | cons op ops ih => exact ih (act_prime h op)

def auxiliary : Fin 4 → Fin 4 := ![1,0,3,2]
def phaseQ : Fin 4 → Q := ![1,1,-qI,qI]

theorem auxiliary_Q : ∀ j a b,
    Kernel.mul (basisQ .exotic (auxiliary j)) Signature.disequality a b=
      phaseQ j*basisQ .exotic j a b := by
  intro j a b
  fin_cases j <;> cases a <;> cases b <;> decide +kernel

theorem auxiliary_matrix (j : Fin 4) :
    Kernel.mul (E .exotic (auxiliary j)) Signature.disequality=scale (embed (phaseQ j)) (E .exotic j) := by
  funext a b
  have h := congrArg embed (auxiliary_Q j a b)
  cases b <;> simpa [Kernel.mul,E,scale,Signature.disequality] using h

theorem phase_ne_zero (j : Fin 4) : embed (phaseQ j)≠0 := by
  apply (map_ne_zero embed).mpr
  fin_cases j <;> decide +kernel

def localScalar {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (j : Fin 4) : Scalar :=
  reps.multiplier (auxiliary j)*embed (phaseQ j)

theorem localScalar_ne_zero {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (j : Fin 4) :
    localScalar reps j≠0 := mul_ne_zero (reps.multiplier_ne_zero _) (phase_ne_zero j)

theorem local_scale_action (T : Mat) (c : Scalar) (i : Fin 4) (q : Signature Scalar 4) :
    Signature.coordinateAction (fun j => if j=i then scale c T else Signature.equality) q=
      c • Signature.coordinateAction (fun j => if j=i then T else Signature.equality) q := by
  funext w
  simp only [Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,Fin.prod_univ_succ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  fin_cases i <;> simp [scale] <;> ring

theorem actual_local {F : SignatureFamily Scalar} (reps : Representatives F .exotic)
    (q : Signature Scalar 4) (i j : Fin 4) :
    onePort q i (reps.matrix (auxiliary j))=localScalar reps j • act (E .exotic) (.dress i j) q := by
  rw [onePort,reps.normal_form,scale_mul_left,auxiliary_matrix]
  have hs : scale (reps.multiplier (auxiliary j)) (scale (embed (phaseQ j)) (E .exotic j))=
      scale (localScalar reps j) (E .exotic j) := by funext a b; simp [scale,localScalar,mul_assoc]
  rw [hs,local_scale_action,act,site_coordinate]

def actualAct {F : SignatureFamily Scalar} (reps : Representatives F .exotic) : Op → Signature Scalar 4 → Signature Scalar 4
  | .dress i j,q => onePort q i (reps.matrix (auxiliary j))
  | .swap i,q => Tensor.reindex (swapPorts i) q
def actualRun {F : SignatureFamily Scalar} (reps : Representatives F .exotic) : List Op → Signature Scalar 4 → Signature Scalar 4
  | [],q => q
  | op::ops,q => actualRun reps ops (actualAct reps op q)
def stepScalar {F : SignatureFamily Scalar} (reps : Representatives F .exotic) : Op → Scalar
  | .dress _ j => localScalar reps j
  | .swap _ => 1
def programScalar {F : SignatureFamily Scalar} (reps : Representatives F .exotic) : List Op → Scalar
  | [] => 1
  | op::ops => programScalar reps ops*stepScalar reps op

theorem actualAct_scale {F : SignatureFamily Scalar} (reps : Representatives F .exotic)
    (op : Op) (q : Signature Scalar 4) : actualAct reps op q=stepScalar reps op • act (E .exotic) op q := by
  cases op with
  | dress i j => exact actual_local reps q i j
  | swap i => simp [actualAct,stepScalar,act]

theorem actualRun_scale {F : SignatureFamily Scalar} (reps : Representatives F .exotic)
    (ops : List Op) (q : Signature Scalar 4) :
    actualRun reps ops q=programScalar reps ops • run (E .exotic) ops q := by
  induction ops generalizing q with
  | nil => simp [actualRun,programScalar,run]
  | cons op ops ih => rw [actualRun,ih,actualAct_scale,run_smul,smul_smul]; rfl

theorem programScalar_ne_zero {F : SignatureFamily Scalar} (reps : Representatives F .exotic) (ops : List Op) :
    programScalar reps ops≠0 := by
  induction ops with
  | nil => exact one_ne_zero
  | cons op ops ih =>
    apply mul_ne_zero ih
    cases op
    · exact localScalar_ne_zero reps _
    · exact one_ne_zero

end Holant.Certificates.EqualityQuaternary.Klein.Orbit
