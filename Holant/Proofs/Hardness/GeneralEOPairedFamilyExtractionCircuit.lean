import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionCircuitBits

/-! Literal fixed-minor realization of a finite batch of affine Boolean maps.
The derived fourth power parity gate forces one unique private assignment, so
summation introduces only an explicit nonzero scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionCircuit
open Holant Holant.Tractable AffinePhase TwoTranslate
open scoped BigOperators
namespace C
export GeneralEOPairedFamilyExtractionCircuitBits
  (coefficient input address assignment assignment_at Consistent consistent_iff partialBit_last)
end C
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle
  (evaluate evaluate_append evaluate_flatten evaluate_replicate)
end B
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose substitute_compose)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable

variable {m n r : ℕ}

abbrev privateCount (m n r : ℕ) := (r*n)*(m+1)

def privatePort (v : Fin r) (i : Fin n) (t : Fin (m+1)) : Bool ⊕ Fin (m+privateCount m n r) :=
  Sum.inr (Fin.natAdd m (C.address v i t))

def inputPort (p : Word m → Word n) (i : Fin n) (j : Fin m) : Bool ⊕ Fin (m+privateCount m n r) :=
  if residueBit (C.coefficient p i j) then Sum.inr (Fin.castAdd (privateCount m n r) j) else Sum.inl false

def gatePorts (ps : Fin r → Word m → Word n) (v : Fin r) (i : Fin n) (t : Fin (m+1)) :
    Fin 3 → Bool ⊕ Fin (m+privateCount m n r) :=
  Fin.cases ![Sum.inl (ps v (origin m) i),Sum.inl false,privatePort v i 0]
    (fun j=>![privatePort v i j.castSucc,inputPort (ps v) i j,privatePort v i j.succ]) t

def outputPorts (v : Fin r) : Fin n → Bool ⊕ Fin (m+privateCount m n r) :=
  fun i=>privatePort v i (Fin.last m)

def gateAt (ps : Fin r → Word m → Word n) (a : Fin (privateCount m n r)) :=
  let vt := finProdFinEquiv.symm a
  let vi := finProdFinEquiv.symm vt.1
  gatePorts ps vi.1 vi.2 vt.2

def ports (ps : Fin r → Word m → Word n) (q : Fin n → Bool ⊕ Fin 3) :
    List (Fin n → Bool ⊕ Fin (m+privateCount m n r)) :=
  List.ofFn outputPorts ++ (List.ofFn (fun a=>List.replicate 4 (I.compose q (gateAt ps a)))).flatten

@[simp] theorem read_private (z : Word m) (y : Word (privateCount m n r))
    (v : Fin r) (i : Fin n) (t : Fin (m+1)) :
    Sum.elim id (Fin.addCases z y) (privatePort v i t)=y (C.address v i t) := by simp [privatePort]

@[simp] theorem read_input (ps : Fin r → Word m → Word n) (z : Word m)
    (y : Word (privateCount m n r)) (v : Fin r) (i : Fin n) (j : Fin m) :
    Sum.elim id (Fin.addCases z y) (inputPort (ps v) i j)=C.input (ps v) z i j := by
  unfold inputPort C.input
  split <;> simp

theorem parity_iff (a b c : Bool) : Bool.xor (Bool.xor a b) c=false ↔ c=Bool.xor a b := by
  cases a <;> cases b <;> cases c <;> decide

def gateHolds (ps : Fin r → Word m → Word n) (z : Word m)
    (y : Word (privateCount m n r)) (a : Fin (privateCount m n r)) : Prop :=
  let w := T.substitute (gateAt ps a) (Fin.addCases z y)
  Bool.xor (Bool.xor (w 0) (w 1)) (w 2)=false

theorem gates_iff (ps : Fin r → Word m → Word n) (z : Word m)
    (y : Word (privateCount m n r)) : (∀a,gateHolds ps z y a) ↔ C.Consistent ps z y := by
  have hh (v : Fin r) (i : Fin n) (t : Fin (m+1)) :
      gateHolds ps z y (C.address v i t) ↔
        Fin.cases (y (C.address v i 0)=ps v (origin m) i)
          (fun j=>y (C.address v i j.succ)=Bool.xor (y (C.address v i j.castSucc)) (C.input (ps v) z i j)) t := by
    simp only [gateHolds,gateAt,C.address,Equiv.symm_apply_apply]
    refine Fin.cases ?_ (fun j=>?_) t
    · simp only [gatePorts,Fin.cases_zero,T.substitute,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,Sum.elim_inl,id_eq,read_private]
      simpa only [Bool.xor_false,C.address] using parity_iff (ps v (origin m) i) false (y (C.address v i 0))
    · simp only [gatePorts,Fin.cases_succ,T.substitute,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,read_private,read_input]
      exact parity_iff _ _ _
  constructor
  · intro h v i
    refine ⟨?_,fun j=>?_⟩
    · exact (hh v i 0).mp (h _)
    · exact (hh v i j.succ).mp (h _)
  · intro h a
    obtain ⟨⟨vi,t⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨v,i⟩,rfl⟩ := finProdFinEquiv.surjective vi
    apply (hh v i t).mpr
    exact Fin.cases (h v i).1 (h v i).2 t

variable (f : Signature AlgebraicComplex n) (q : Fin n → Bool ⊕ Fin 3) (c : AlgebraicComplex)
variable (hq : ∀w : Word 3,f (T.substitute q w)^4=
  if Bool.xor (Bool.xor (w 0) (w 1)) (w 2)=false then c else 0)

include hq in
theorem gates_value (ps : Fin r → Word m → Word n) (z : Word m) (y : Word (privateCount m n r)) :
    B.evaluate f ((List.ofFn (fun a=>List.replicate 4 (I.compose q (gateAt ps a)))).flatten)
      (Fin.addCases z y)=if C.Consistent ps z y then c^(privateCount m n r) else 0 := by
  rw [B.evaluate_flatten]
  simp only [List.map_ofFn,Function.comp_def,B.evaluate_replicate,I.substitute_compose,hq,List.prod_ofFn]
  have prod_indicator (b : Fin (privateCount m n r) → Prop) :
      (∏a,if b a then c else 0)=if ∀a,b a then c^(privateCount m n r) else 0 := by
    by_cases h : ∀a,b a
    · simp [h]
    · obtain ⟨a,ha⟩ := not_forall.mp h
      simp only [h,ite_false]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])
  have he := prod_indicator (gateHolds ps z y)
  have he' : (∏a,if gateHolds ps z y a then c else 0)=
      if C.Consistent ps z y then c^(privateCount m n r) else 0 := by
    simpa only [gates_iff] using he
  calc
    _=(∏a,if gateHolds ps z y a then c else 0) := by
      apply Finset.prod_congr rfl
      intro a _
      by_cases h : gateHolds ps z y a
      · have hh := h
        unfold gateHolds at hh
        simp only [h,hh,ite_true]
      · have hh := h
        unfold gateHolds at hh
        simp only [h,hh,ite_false]
    _=_ := he'

theorem outputs_value (ps : Fin r → Word m → Word n) (hp : ∀v,IsAffineMap (ps v)) (z : Word m) :
    B.evaluate f (List.ofFn outputPorts) (Fin.addCases z (C.assignment ps z))=∏v,f (ps v z) := by
  simp only [B.evaluate,List.map_ofFn,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro v _
  apply congrArg f
  funext i
  simp only [T.substitute,outputPorts,read_private,C.assignment_at,C.partialBit_last _ (hp v)]

include hq in
theorem value (ps : Fin r → Word m → Word n) (hp : ∀v,IsAffineMap (ps v)) (z : Word m) :
    (∑y : Word (privateCount m n r),B.evaluate f (ports ps q) (Fin.addCases z y))=
      c^(privateCount m n r)*∏v,f (ps v z) := by
  have he (y : Word (privateCount m n r)) : B.evaluate f (ports ps q) (Fin.addCases z y)=
      if y=C.assignment ps z then c^(privateCount m n r)*∏v,f (ps v z) else 0 := by
    rw [ports,B.evaluate_append,gates_value f q c hq,C.consistent_iff]
    by_cases hy : y=C.assignment ps z
    · subst y
      simp only [ite_true,outputs_value f ps hp z]
      exact mul_comm _ _
    · simp only [hy,ite_false,mul_zero]
  simp_rw [he]
  simp

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionCircuit
