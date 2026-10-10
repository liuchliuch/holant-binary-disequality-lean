import Holant.ReedMuller.WeightTwoIntegration.ExceptionalAlgebra
import Holant.NetworkGluing.Finite

/-! The fixed original-port incidence of the six-port exception. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace ExceptionalTopology

def canonicalPorts : (Fin 3 × Bool) ≃ Fin 6 :=
  (Equiv.prodCongr (Equiv.refl (Fin 3)) finTwoEquiv.symm).trans finProdFinEquiv

theorem canonicalPorts_values :
    canonicalPorts (0,false) = 0 ∧ canonicalPorts (0,true) = 1 ∧
    canonicalPorts (1,false) = 2 ∧ canonicalPorts (1,true) = 3 ∧
    canonicalPorts (2,false) = 4 ∧ canonicalPorts (2,true) = 5 := by decide

def ports : (Σ _ : Bool, Fin 6) ≃ Fin 4 ⊕ (Fin 4 × Bool) where
  toFun p := if p.1 then
    ![.inr (0,true),.inr (1,true),.inr (2,false),.inr (3,false),
      .inr (2,true),.inr (3,true)] p.2
    else ![.inl 0,.inl 1,.inl 2,.inl 3,.inr (0,false),.inr (1,false)] p.2
  invFun p := match p with
    | .inl i => ![⟨false,0⟩,⟨false,1⟩,⟨false,2⟩,⟨false,3⟩] i
    | .inr (i,false) => ![⟨false,4⟩,⟨false,5⟩,⟨true,2⟩,⟨true,3⟩] i
    | .inr (i,true) => ![⟨true,0⟩,⟨true,1⟩,⟨true,4⟩,⟨true,5⟩] i
  left_inv := by rintro ⟨b,i⟩; cases b <;> fin_cases i <;> rfl
  right_inv := by rintro (i|⟨i,b⟩); fin_cases i <;> rfl; cases b <;> fin_cases i <;> rfl

def network (q : Signature ℂ 6) (C : Fin 4 → Kernel ℂ) :
    FiniteNetwork ℂ Bool (Fin 4) 4 where
  arity := fun _ => 6
  ports := ports
  vertex := fun _ => q
  edge := C

/-- Original pairs are literally (0,1), (2,3), and (4,5). -/
def paired (h : Bool → Bool → Bool → ℂ) : Signature ℂ 6 := fun x =>
  if x 0 = x 1 ∧ x 2 = x 3 ∧ x 4 = x 5 then h (x 0) (x 2) (x 4) else 0

def diagonal (s : ℂ) : Kernel ℂ := fun a b => if a = b then s ^ (if a then 1 else 0) else 0

/-- Sign parity is placed on the first link of each pair. -/
def characters (eta theta : ℂ) : Fin 4 → Kernel ℂ :=
  ![diagonal eta,diagonal 1,diagonal theta,diagonal 1]

def pairedOutput (Q : Bool → Bool → ℂ) : Signature ℂ 4 := fun x =>
  if x 0 = x 1 ∧ x 2 = x 3 then Q (x 0) (x 2) else 0

def logicalSum (h : Bool → Bool → Bool → ℂ) (eta theta : ℂ) (x y : Bool) : ℂ :=
  ∑ a : Bool, ∑ c : Bool,
    eta ^ (if a then 1 else 0) * theta ^ (if c then 1 else 0) * h x y a * h a c c

def edgeAssignments : ((Fin 4 × Bool) → Bool) ≃
    ((Fin 4 → Bool) × (Fin 4 → Bool)) where
  toFun z := (fun i => z (i,false),fun i => z (i,true))
  invFun p q := if q.2 then p.2 q.1 else p.1 q.1
  left_inv := by intro z; funext q; rcases q with ⟨i,b⟩; cases b <;> rfl
  right_inv := by rintro ⟨a,b⟩; rfl

theorem sum_words_succ (n : ℕ) (f : (Fin (n+1) → Bool) → ℂ) :
    (∑ x, f x) = ∑ a : Bool, ∑ x : Fin n → Bool, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f,Fintype.sum_prod_type]
  rfl

def words4 : (Fin 4 → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun w := (w 0,w 1,w 2,w 3)
  invFun w := ![w.1,w.2.1,w.2.2.1,w.2.2.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem sum_words4 [DecidableEq (Fin 4)] (f : (Fin 4 → Bool) → ℂ) :
    (∑ x, f x) = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f ![a,b,c,d] := by
  rw [← words4.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Every surviving assignment has exactly the two common logical bits a,c. -/
theorem logical_network (h : Bool → Bool → Bool → ℂ) (eta theta : ℂ) :
    (network (paired h) (characters eta theta)).denote =
      pairedOutput (logicalSum h eta theta) := by
  classical
  let : DecidableEq (Fin 4) := Classical.decEq _
  funext x
  simp only [FiniteNetwork.denote]
  change (∑ z : Fin 4 × Bool → Bool,
    (∏ v : Bool, paired h (fun i : Fin 6 => Sum.elim x z (ports ⟨v,i⟩))) *
      ∏ e : Fin 4, characters eta theta e (z (e,false)) (z (e,true))) = _
  rw [← edgeAssignments.symm.sum_comp,Fintype.sum_prod_type]
  simp only [Fintype.prod_bool,Fin.prod_univ_succ]
  simp only [sum_words4]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [edgeAssignments,ports,paired,characters,diagonal,pairedOutput,logicalSum,
      h0,h1,h2,h3] <;> ring

theorem exceptional_logical_network (d : ExceptionalData) :
    (network (paired d.h) (characters d.eta d.theta)).denote = pairedOutput d.Q :=
  logical_network d.h d.eta d.theta

end ExceptionalTopology
end Holant.ReedMuller.WeightTwoIntegration
