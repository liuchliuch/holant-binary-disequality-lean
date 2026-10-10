import Holant.Proofs.Hardness.BinaryThreeSupportCircuit
import Holant.Proofs.Hardness.BinaryCSPProgrammeCore

/-! Static signed-NAND2 graph rows emitted from the accepted circuit syntax.
There is no COPY gate: repeated input reads refer to the same variable index.
Declared variables include unused original inputs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportGraph
open Holant
open Holant.LocalDrafts.RemoteWork.CountingBridge
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype
namespace C
export BinaryThreeSupportCircuit (Aux auxBits auxEquiv twoEquiv tenEquiv weight sum_weight value value_eq)
end C
namespace G
export BinaryThreeSupportGates (nand sign clause different nandGateWeight)
end G

abbrev Raw := BinaryCSPProgrammeCore.Raw
abbrev Rows := List (ℕ×ℕ) × List ℕ

def append (r s : Rows) : Rows := (r.1++s.1,r.2++s.2)

def nandBlock (x y o : ℕ) : Rows :=
  ([(x,o+1),(o+4,x),(o+4,o+1),
    (y,o+2),(o+5,y),(o+5,o+2),
    (o,o+3),(o+6,o),(o+6,o+3),
    (o+7,x),(o+7,o),(o+8,y),(o+8,o),
    (o+9,o+1),(o+9,o+2),(o+9,o+3)],
    [o+4,o+5,o+6,o+7,o+8,o+9])

def pinBlock (b : Bool) (o : ℕ) : Rows :=
  if b then ([(o+1,o)],[o+1]) else ([(o,o),(o+1,o+1)],[])

def rows {n : ℕ} (c : Circuit n) (env : Fin n→ℕ) (offset : ℕ) : Rows :=
  match c with
  | .output out => ([(offset,env out)],[offset])
  | .constant b c => append (pinBlock b offset) (rows c (Fin.cons offset env) (offset+2))
  | .nand a b c => append (nandBlock (env a) (env b) offset)
      (rows c (Fin.cons offset env) (offset+10))

def compile (c : CircuitInstance) : Raw where
  «variables» := c.inputs+C.auxBits c.circuit
  edges := (rows c.circuit Fin.val c.inputs).1
  signs := (rows c.circuit Fin.val c.inputs).2

def readAux {n : ℕ} (c : Circuit n) (offset : ℕ) (ρ : ℕ→Bool) : C.Aux c :=
  match c with
  | .output _ => ρ offset
  | .constant _ c => (ρ offset,ρ (offset+1),readAux c (offset+2) ρ)
  | .nand _ _ c => (ρ offset,![ρ (offset+1),ρ (offset+2),ρ (offset+3)],
      ![ρ (offset+4),ρ (offset+5),ρ (offset+6)],
      ![ρ (offset+7),ρ (offset+8),ρ (offset+9)],readAux c (offset+10) ρ)

variable {K : Type*} [CommRing K]

def rowsWeight (r : Rows) (ρ : ℕ→Bool) : K :=
  (r.1.map (fun e=>G.nand (ρ e.1) (ρ e.2))).prod * (r.2.map (fun v=>G.sign (ρ v))).prod

theorem append_weight (r s : Rows) (ρ : ℕ→Bool) :
    rowsWeight (K:=K) (append r s) ρ=rowsWeight r ρ*rowsWeight s ρ := by
  simp only [rowsWeight,append,List.map_append,List.prod_append]
  ring

theorem nandBlock_weight (x y o : ℕ) (ρ : ℕ→Bool) :
    rowsWeight (K:=K) (nandBlock x y o) ρ=
      G.nandGateWeight (ρ x) (ρ y) (ρ o)
        ![ρ (o+1),ρ (o+2),ρ (o+3)] ![ρ (o+4),ρ (o+5),ρ (o+6)]
        ![ρ (o+7),ρ (o+8),ρ (o+9)] := by
  simp [rowsWeight,nandBlock,G.nandGateWeight,G.different,G.clause,
    Fin.prod_univ_two,Fin.prod_univ_three]
  ring

theorem pinBlock_weight (b : Bool) (o : ℕ) (ρ : ℕ→Bool) :
    rowsWeight (K:=K) (pinBlock b o) ρ=
      BinaryThreeSupportCircuit.pinWeight b (ρ o) (ρ (o+1)) := by
  cases b <;> simp [rowsWeight,pinBlock,BinaryThreeSupportCircuit.pinWeight,
    G.clause,Fin.prod_univ_succ,mul_comm]

private theorem read_cons {n : ℕ} (ρ : ℕ→Bool) (o : ℕ) (env : Fin n→ℕ) :
    (fun i : Fin (n+1)=>ρ (Fin.cons (α:=fun _=>ℕ) o env i))=
      Fin.cons (α:=fun _=>Bool) (ρ o) (fun i=>ρ (env i)) := by
  funext i
  refine Fin.cases rfl (fun _=>rfl) i

/-- Actual emitted factor rows, with absolute variable addresses, have the
already proved circuit weight for every assignment. -/
theorem rowsWeight_eq {n : ℕ} (c : Circuit n) (env : Fin n→ℕ) (offset : ℕ)
    (ρ : ℕ→Bool) : rowsWeight (K:=K) (rows c env offset) ρ=
      C.weight c (fun i=>ρ (env i)) (readAux c offset ρ) := by
  induction c generalizing offset with
  | output out =>
    simp [rows,rowsWeight,C.weight,readAux,G.clause,Fin.prod_univ_succ,mul_comm]
  | constant b c ih =>
    rw [rows,append_weight,pinBlock_weight,ih]
    simp only [C.weight,readAux,read_cons]
  | nand a b c ih =>
    rw [rows,append_weight,nandBlock_weight,ih]
    simp only [C.weight,readAux,read_cons]

theorem edge_count_le {n : ℕ} (c : Circuit n) (env : Fin n→ℕ) (offset : ℕ) :
    (rows c env offset).1.length≤16*c.gates+1 := by
  induction c generalizing offset with
  | output out => simp [rows,Circuit.gates]
  | constant b c ih =>
    have h := ih (Fin.cons offset env) (offset+2)
    cases b <;> simp only [rows,append,pinBlock,Bool.false_eq_true,ite_false,ite_true,
      List.length_append,List.length_cons,List.length_nil,Circuit.gates] <;> omega
  | nand a b c ih =>
    have h := ih (Fin.cons offset env) (offset+10)
    simp only [rows,append,nandBlock,List.length_append,List.length_cons,List.length_nil,Circuit.gates]
    omega

theorem sign_count_le {n : ℕ} (c : Circuit n) (env : Fin n→ℕ) (offset : ℕ) :
    (rows c env offset).2.length≤6*c.gates+1 := by
  induction c generalizing offset with
  | output out => simp [rows,Circuit.gates]
  | constant b c ih =>
    have h := ih (Fin.cons offset env) (offset+2)
    cases b <;> simp only [rows,append,pinBlock,Bool.false_eq_true,ite_false,ite_true,
      List.length_append,List.length_cons,List.length_nil,Circuit.gates] <;> omega
  | nand a b c ih =>
    have h := ih (Fin.cons offset env) (offset+10)
    simp only [rows,append,nandBlock,List.length_append,List.length_cons,List.length_nil,Circuit.gates]
    omega

theorem compile_resources (c : CircuitInstance) :
    (compile c).variables≤c.inputs+10*c.circuit.gates+1 ∧
    (compile c).edges.length≤16*c.circuit.gates+1 ∧
    (compile c).signs.length≤6*c.circuit.gates+1 := by
  refine ⟨?_,edge_count_le c.circuit _ _,sign_count_le c.circuit _ _⟩
  have h := BinaryThreeSupportCircuit.auxBits_le c.circuit
  simp only [compile]
  omega

def Bounded (r : Rows) (N : ℕ) : Prop :=
  (∀e∈r.1,e.1<N ∧ e.2<N) ∧ ∀v∈r.2,v<N

theorem bounded_mono {r : Rows} {N M : ℕ} (h : Bounded r N) (hNM : N≤M) :
    Bounded r M := ⟨fun e he=>⟨(h.1 e he).1.trans_le hNM,(h.1 e he).2.trans_le hNM⟩,
      fun v hv=>(h.2 v hv).trans_le hNM⟩

theorem append_bounded {r s : Rows} {N : ℕ} (hr : Bounded r N) (hs : Bounded s N) :
    Bounded (append r s) N := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · exact hr.1 e he
    · exact hs.1 e he
  · intro v hv
    rcases List.mem_append.mp hv with hv|hv
    · exact hr.2 v hv
    · exact hs.2 v hv

theorem nandBlock_bounded {x y o : ℕ} (hx : x<o) (hy : y<o) :
    Bounded (nandBlock x y o) (o+10) := by
  constructor
  · intro e he
    simp only [nandBlock,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [Prod.fst,Prod.snd] <;> omega
  · intro v hv
    simp only [nandBlock,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem pinBlock_bounded (b : Bool) (o : ℕ) : Bounded (pinBlock b o) (o+2) := by
  cases b <;> simp [Bounded,pinBlock] <;> omega

theorem rows_bounded {n : ℕ} (c : Circuit n) (env : Fin n→ℕ) (offset : ℕ)
    (he : ∀i,env i<offset) : Bounded (rows c env offset) (offset+C.auxBits c) := by
  induction c generalizing offset with
  | output out =>
    have h := he out
    simp [rows,Bounded,C.auxBits]
    omega
  | constant b c ih =>
    have he' : ∀i,Fin.cons (α:=fun _=>ℕ) offset env i<offset+2 := by
      intro i
      refine Fin.cases (by simp) (fun j=>?_) i
      simp only [Fin.cons_succ]
      exact (he j).trans (by omega)
    have ht := ih (Fin.cons offset env) (offset+2) he'
    have hh := bounded_mono (pinBlock_bounded b offset)
      (Nat.le_add_right (offset+2) (C.auxBits c))
    simpa only [rows,C.auxBits,Nat.add_assoc] using append_bounded hh ht
  | nand a b c ih =>
    have he' : ∀i,Fin.cons (α:=fun _=>ℕ) offset env i<offset+10 := by
      intro i
      refine Fin.cases (by simp) (fun j=>?_) i
      simp only [Fin.cons_succ]
      exact (he j).trans (by omega)
    have ht := ih (Fin.cons offset env) (offset+10) he'
    have hh := bounded_mono (nandBlock_bounded (he a) (he b))
      (Nat.le_add_right (offset+10) (C.auxBits c))
    simpa only [rows,C.auxBits,Nat.add_assoc] using append_bounded hh ht

theorem compile_wellFormed (c : CircuitInstance) : (compile c).WellFormed :=
  rows_bounded c.circuit Fin.val c.inputs (fun i=>i.isLt)

theorem auxEquiv_read {n : ℕ} (c : Circuit n) (offset : ℕ) (ρ : ℕ→Bool) :
    C.auxEquiv c (fun i=>ρ (offset+i.val))=readAux c offset ρ := by
  induction c generalizing offset with
  | output out => rfl
  | constant b c ih =>
    change (ρ offset,ρ (offset+1),C.auxEquiv c (fun i=>ρ (offset+(2+i.val))))=
      (ρ offset,ρ (offset+1),readAux c (offset+2) ρ)
    simpa only [Nat.add_assoc] using
      congrArg (fun z=>(ρ offset,ρ (offset+1),z)) (ih (offset+2))
  | nand a b c ih =>
    change (ρ offset,![ρ (offset+1),ρ (offset+2),ρ (offset+3)],
      ![ρ (offset+4),ρ (offset+5),ρ (offset+6)],![ρ (offset+7),ρ (offset+8),ρ (offset+9)],
      C.auxEquiv c (fun i=>ρ (offset+(10+i.val))))=
      (ρ offset,![ρ (offset+1),ρ (offset+2),ρ (offset+3)],
      ![ρ (offset+4),ρ (offset+5),ρ (offset+6)],![ρ (offset+7),ρ (offset+8),ρ (offset+9)],
      readAux c (offset+10) ρ)
    simpa only [Nat.add_assoc] using
      congrArg (fun z=>(ρ offset,![ρ (offset+1),ρ (offset+2),ρ (offset+3)],
        ![ρ (offset+4),ρ (offset+5),ρ (offset+6)],
        ![ρ (offset+7),ρ (offset+8),ρ (offset+9)],z)) (ih (offset+10))

def extend {N : ℕ} (z : Fin N→Bool) (i : ℕ) : Bool := if h : i<N then z ⟨i,h⟩ else false

@[simp] theorem extend_apply {N : ℕ} (z : Fin N→Bool) (i : Fin N) : extend z i.val=z i := by
  simp [extend,i.isLt]

def assignmentEquiv (c : CircuitInstance) :
    (Fin (compile c).variables→Bool) ≃ ((Fin c.inputs→Bool)×C.Aux c.circuit) :=
  (CircuitSemantics.blockEquiv c.inputs (C.auxBits c.circuit)).trans
    (Equiv.prodCongr (Equiv.refl _) (C.auxEquiv c.circuit))

theorem assignment_row (c : CircuitInstance) (z : Fin (compile c).variables→Bool) :
    rowsWeight (K:=K) ((compile c).edges,(compile c).signs) (extend z)=
      C.weight c.circuit (assignmentEquiv c z).1 (assignmentEquiv c z).2 := by
  change rowsWeight (rows c.circuit Fin.val c.inputs) (extend z)=_
  rw [rowsWeight_eq,←auxEquiv_read]
  congr 1
  · funext i
    change extend z i.val=z (Fin.castAdd (C.auxBits c.circuit) i)
    exact extend_apply z (Fin.castAdd _ i)
  · congr 1
    funext i
    change extend z (c.inputs+i.val)=z (Fin.natAdd c.inputs i)
    exact extend_apply z (Fin.natAdd c.inputs i)

def value (r : Raw) : K :=
  ∑z : Fin r.variables→Bool,rowsWeight (r.edges,r.signs) (extend z)

/-- Literal flat-graph count equality. The declared input slots preserve a
factor of two for every unused source witness variable. -/
theorem compile_value (c : CircuitInstance) : value (K:=K) (compile c)=(c.value : K) := by
  rw [←C.value_eq]
  unfold value C.value
  simp_rw [assignment_row]
  rw [←(assignmentEquiv c).symm.sum_comp]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportGraph
