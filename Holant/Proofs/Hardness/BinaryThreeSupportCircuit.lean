import Holant.Proofs.Hardness.BinaryThreeSupportGates

/-! An actual finite signed independent-set reduction of the accepted NAND
circuit syntax. Every source input remains a summation variable, including
unused inputs. All fresh choices and their literal NAND2/sign factors are
constructed from the syntax. No target evaluation or count identity is an
argument. A physical byte compiler remains a separate obligation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportCircuit
open Holant Holant.Complexity
open Holant.LocalDrafts.RemoteWork.CountingBridge
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
local instance : Fintype Bool := Bool.fintype
namespace G
export BinaryThreeSupportGates (nand sign clause clause_sum nandGateWeight nandGate_sum)
end G

def Aux {n : ℕ} : Circuit n→Type
  | .output _ => Bool
  | .constant _ c => Bool × Bool × Aux c
  | .nand _ _ c => Bool × (Fin 3→Bool) × (Fin 3→Bool) × (Fin 3→Bool) × Aux c

instance auxFintype : {n : ℕ}→(c : Circuit n)→Fintype (Aux c)
  | _,.output _ => Bool.fintype
  | _,.constant _ c => by
    letI : Fintype (Aux c) := auxFintype c
    exact inferInstanceAs (Fintype (Bool × Bool × Aux c))
  | _,.nand _ _ c => by
    letI : Fintype (Aux c) := auxFintype c
    exact inferInstanceAs (Fintype (Bool × (Fin 3→Bool) × (Fin 3→Bool) × (Fin 3→Bool) × Aux c))

def auxBits {n : ℕ} : Circuit n→ℕ
  | .output _ => 1
  | .constant _ c => 2+auxBits c
  | .nand _ _ c => 10+auxBits c

theorem auxBits_le {n : ℕ} (c : Circuit n) : auxBits c≤10*c.gates+1 := by
  induction c with
  | output _ => simp [auxBits,Circuit.gates]
  | constant _ c ih => simp only [auxBits,Circuit.gates]; omega
  | nand _ _ c ih => simp only [auxBits,Circuit.gates]; omega

def twoEquiv : (Fin 2→Bool) ≃ (Bool×Bool) where
  toFun z := (z 0,z 1)
  invFun z := ![z.1,z.2]
  left_inv := by intro z; funext i; fin_cases i <;> rfl
  right_inv := by intro z; rfl

def tenEquiv : (Fin 10→Bool) ≃
    (Bool × (Fin 3→Bool) × (Fin 3→Bool) × (Fin 3→Bool)) where
  toFun z := (z 0,![z 1,z 2,z 3],![z 4,z 5,z 6],![z 7,z 8,z 9])
  invFun z := ![z.1,z.2.1 0,z.2.1 1,z.2.1 2,z.2.2.1 0,z.2.2.1 1,z.2.2.1 2,
    z.2.2.2 0,z.2.2.2 1,z.2.2.2 2]
  left_inv := by intro z; funext i; fin_cases i <;> rfl
  right_inv := by
    rintro ⟨o,r,s,t⟩
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
      funext i <;> fin_cases i <;> rfl

/-- Every declared fresh bit is used once as an auxiliary coordinate. -/
def auxEquiv : {n : ℕ}→(c : Circuit n)→(Fin (auxBits c)→Bool) ≃ Aux c
  | _,.output _ => (show (Fin 1→Bool) ≃ Bool from {
      toFun := fun z=>z 0
      invFun := fun b _=>b
      left_inv := by intro z; funext i; fin_cases i; rfl
      right_inv := fun _=>rfl })
  | _,.constant _ c =>
    (CircuitSemantics.blockEquiv 2 (auxBits c)).trans
      ((Equiv.prodCongr twoEquiv (auxEquiv c)).trans (Equiv.prodAssoc _ _ _))
  | _,.nand _ _ c =>
    (CircuitSemantics.blockEquiv 10 (auxBits c)).trans
      ((Equiv.prodCongr tenEquiv (auxEquiv c)).trans
        ((Equiv.prodAssoc _ _ _).trans
          (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodAssoc _ _ _).trans
            (Equiv.prodCongr (Equiv.refl _) (Equiv.prodAssoc _ _ _))))))

variable {K : Type*} [CommRing K]

/-- The false-constant auxiliary is forced to zero by an actual self-loop,
so constants do not add an accidental factor of two. -/
def pinWeight (b o t : Bool) : K :=
  if b then G.clause ![o] t else G.nand o o*G.nand t t

theorem pinWeight_sum (b o : Bool) :
    (∑t : Bool,pinWeight (K:=K) b o t)=if o=b then 1 else 0 := by
  cases b <;> cases o <;> simp [pinWeight,G.clause,G.nand,G.sign,Fintype.sum_bool,Fin.prod_univ_succ]

def weight {n : ℕ} (c : Circuit n) (x : Fin n→Bool) (z : Aux c) : K :=
  match c,z with
  | .output out,z => G.clause ![x out] z
  | .constant b c,(o,t,z) => pinWeight b o t * weight c (Fin.cons o x) z
  | .nand a b c,(o,r,s,t,z) =>
    G.nandGateWeight (x a) (x b) o r s t * weight c (Fin.cons o x) z

theorem sum_weight {n : ℕ} (c : Circuit n) (x : Fin n→Bool) :
    (∑z : Aux c,weight (K:=K) c x z)=if c.eval x then 1 else 0 := by
  induction c with
  | output out =>
    change (∑z : Bool,G.clause (K:=K) ![x out] z)=_
    rw [G.clause_sum]
    cases hx : x out <;> simp [Circuit.eval,Fin.exists_fin_succ,hx]
  | constant b c ih =>
    change (∑z : Bool×Bool×Aux c,pinWeight (K:=K) b z.1 z.2.1 *
      weight c (Fin.cons z.1 x) z.2.2)=_
    simp only [Fintype.sum_prod_type]
    simp_rw [←Finset.mul_sum,ih,←Finset.sum_mul,pinWeight_sum]
    cases b <;> simp [Fintype.sum_bool,Circuit.eval]
  | nand a b c ih =>
    change (∑z : Bool×(Fin 3→Bool)×(Fin 3→Bool)×(Fin 3→Bool)×Aux c,
      G.nandGateWeight (K:=K) (x a) (x b) z.1 z.2.1 z.2.2.1 z.2.2.2.1 *
        weight c (Fin.cons z.1 x) z.2.2.2.2)=_
    simp only [Fintype.sum_prod_type]
    simp_rw [←Finset.mul_sum,ih,←Finset.sum_mul,G.nandGate_sum]
    cases ha : x a <;> cases hb : x b <;> simp [Fintype.sum_bool,Gates.nand,Circuit.eval,ha,hb]

def value (c : CircuitInstance) : K :=
  ∑x : Fin c.inputs→Bool,∑z : Aux c.circuit,weight c.circuit x z

/-- Count equality for every literal accepted circuit, with isolated source
inputs preserved automatically by the outer sum. -/
theorem value_eq (c : CircuitInstance) : value (K:=K) c=(c.value : K) := by
  unfold value
  simp_rw [sum_weight]
  simp [CircuitInstance.value,countAccepted,Nat.cast_sum]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportCircuit
