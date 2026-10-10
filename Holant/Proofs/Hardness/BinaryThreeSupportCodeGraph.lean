import Holant.Proofs.Hardness.BinaryThreeSupportGraph

/-! A static code-row description of the concrete signed circuit compiler.
Every operand address is computed from a prefix sum and a reverse index, so
the physical programme can tabulate rows without an assumed recursive parser
or an external environment invariant. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportCodeGraph
open Holant.LocalDrafts.RemoteWork.CountingBridge
namespace G
export BinaryThreeSupportGraph (Raw Rows append pinBlock nandBlock rows compile)
end G
set_option backward.isDefEq.respectTransparency false

def fresh (r : Circuit.Row) : ℕ := if r.1<2 then 2 else 10

def start (rs : List Circuit.Row) (offset t : ℕ) : ℕ :=
  offset+((rs.take t).map fresh).sum

def resolve (rs : List Circuit.Row) (env : ℕ→ℕ) (offset t u : ℕ) : ℕ :=
  if u<t then start rs offset (t-1-u) else env (u-t)

def push (o : ℕ) (env : ℕ→ℕ) (u : ℕ) : ℕ := if u=0 then o else env (u-1)

def block (r : Circuit.Row) (env : ℕ→ℕ) (offset : ℕ) : G.Rows :=
  if r.1<2 then G.pinBlock (r.1=1) offset else G.nandBlock (env r.2.1) (env r.2.2) offset

def blockAt (rs : List Circuit.Row) (env : ℕ→ℕ) (offset t : ℕ) : G.Rows :=
  block (rs.getD t (0,(0,0))) (resolve rs env offset t) (start rs offset t)

def staticRows (rs : List Circuit.Row) (out : ℕ) (env : ℕ→ℕ) (offset : ℕ) : G.Rows :=
  ((List.range rs.length).flatMap (fun t=>(blockAt rs env offset t).1) ++
      [(start rs offset rs.length,resolve rs env offset rs.length out)],
    (List.range rs.length).flatMap (fun t=>(blockAt rs env offset t).2) ++
      [start rs offset rs.length])

@[simp] theorem start_zero (rs : List Circuit.Row) (offset : ℕ) : start rs offset 0=offset := by
  simp [start]

theorem start_cons (r : Circuit.Row) (rs : List Circuit.Row) (offset t : ℕ) :
    start (r::rs) offset (t+1)=start rs (offset+fresh r) t := by
  simp [start,List.take_succ_cons,Nat.add_assoc]

theorem resolve_cons (r : Circuit.Row) (rs : List Circuit.Row) (env : ℕ→ℕ) (offset t u : ℕ) :
    resolve (r::rs) env offset (t+1) u=
      resolve rs (push offset env) (offset+fresh r) t u := by
  by_cases hu : u<t
  · have hu' : u<t+1 := by omega
    have hi : t+1-1-u=(t-1-u)+1 := by omega
    rw [resolve,resolve,ite_eq_left hu',ite_eq_left hu,hi,start_cons]
  · by_cases he : u=t
    · subst u
      simp [resolve,push]
    · have hu' : ¬u<t+1 := by omega
      have hz : u-t≠0 := by omega
      rw [resolve,resolve,ite_eq_right hu',ite_eq_right hu,push,ite_eq_right hz]
      congr 1

@[simp] theorem blockAt_zero (r : Circuit.Row) (rs : List Circuit.Row)
    (env : ℕ→ℕ) (offset : ℕ) : blockAt (r::rs) env offset 0=block r env offset := by
  have h : resolve (r::rs) env offset 0=env := by funext u; simp [resolve]
  simp [blockAt,h]

theorem blockAt_succ (r : Circuit.Row) (rs : List Circuit.Row)
    (env : ℕ→ℕ) (offset t : ℕ) :
    blockAt (r::rs) env offset (t+1)=blockAt rs (push offset env) (offset+fresh r) t := by
  simp only [blockAt,start_cons]
  have he : resolve (r::rs) env offset (t+1)=resolve rs (push offset env) (offset+fresh r) t :=
    funext (resolve_cons r rs env offset t)
  rw [he]
  rfl

theorem staticRows_nil (out : ℕ) (env : ℕ→ℕ) (offset : ℕ) :
    staticRows [] out env offset=([(offset,env out)],[offset]) := by
  simp [staticRows,start,resolve]

theorem staticRows_cons (r : Circuit.Row) (rs : List Circuit.Row)
    (out : ℕ) (env : ℕ→ℕ) (offset : ℕ) :
    staticRows (r::rs) out env offset=
      G.append (block r env offset) (staticRows rs out (push offset env) (offset+fresh r)) := by
  simp [staticRows,List.range_succ_eq_map,List.flatMap_map,blockAt_succ,start_cons,
    resolve_cons,G.append,List.append_assoc]

private theorem push_fin {n : ℕ} (env : ℕ→ℕ) (offset : ℕ) :
    (fun i : Fin (n+1)=>push offset env i.val)=
      Fin.cons (α:=fun _=>ℕ) offset (fun i : Fin n=>env i.val) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;> simp [push]

theorem staticRows_exact {n : ℕ} (c : Circuit n) (env : ℕ→ℕ) (offset : ℕ) :
    staticRows c.code.1 c.code.2 env offset=G.rows c (fun i=>env i.val) offset := by
  induction c generalizing env offset with
  | output out => exact staticRows_nil out.val env offset
  | constant b c ih =>
    cases b <;>
      simp only [Circuit.code,Bool.false_eq_true,ite_false,ite_true,staticRows_cons,
        block,fresh,show (0 : ℕ)<2 by decide,ite_true,show (1 : ℕ)<2 by decide,
        show (0 : ℕ)=1 ↔ False by decide,decide_false,decide_true]
    all_goals rw [ih,push_fin]
    all_goals rfl
  | nand a b c ih =>
    simp only [Circuit.code,staticRows_cons,block,fresh,lt_self_iff_false,ite_false]
    rw [ih,push_fin]
    rfl

theorem fresh_sum {n : ℕ} (c : Circuit n) :
    (c.code.1.map fresh).sum+1=BinaryThreeSupportCircuit.auxBits c := by
  induction c with
  | output out => rfl
  | constant b c ih => cases b <;> simp [Circuit.code,fresh,BinaryThreeSupportCircuit.auxBits,←ih,Nat.add_assoc]
  | nand a b c ih => simp [Circuit.code,fresh,BinaryThreeSupportCircuit.auxBits,←ih,Nat.add_assoc]

def compile (c : CircuitInstance) : G.Raw where
  «variables» := start c.circuit.code.1 c.inputs c.circuit.code.1.length+1
  edges := (staticRows c.circuit.code.1 c.circuit.code.2 id c.inputs).1
  signs := (staticRows c.circuit.code.1 c.circuit.code.2 id c.inputs).2

/-- This tabulation is exactly the validated, counted recursive graph writer. -/
theorem compile_exact (c : CircuitInstance) : compile c=G.compile c := by
  simp only [compile,G.compile,staticRows_exact,id_eq]
  congr 1
  simp only [start,List.take_length,Nat.add_assoc,fresh_sum]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportCodeGraph
