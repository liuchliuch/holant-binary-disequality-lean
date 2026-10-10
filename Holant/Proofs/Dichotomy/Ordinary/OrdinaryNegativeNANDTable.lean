import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNANDSource
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinarySquareProgramme

/-! A literal unsigned binary-CSP tape compiler into a selected ordinary
table. Each edge emits precisely one labelled two-port row; the variable
header is copied, including unused variables. The old sign field is ignored
because the source evaluator is the unsigned partition function. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDTable
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.MainChain Holant.OneHot
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
namespace C
export BinaryCSPProgrammeCore (Raw encoding edgeEncoding edgesEncoding variablesComputes edgesComputes)
end C
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace V
export BinaryCSPProgrammeValue (value assignment weight)
end V
namespace E
export Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction (Raw Factor)
namespace Raw
export Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw
  (factorEncoding encoding factor_count_le_length variable_count_le_length)
end Raw
end E
namespace O
export StableHigherCurrentOrdinarySquare (Valid value weight rowValue extend square)
export StableHigherCurrentOrdinarySquareProgramme (Input inputEncoding)
end O
namespace A
export Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access (cons list₁)
end A
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (mapComputes)
end W

def row (j : ℕ) (e : ℕ × ℕ) : E.Factor := (j,[e.1,e.2])
def raw (j : ℕ) (r : C.Raw) : E.Raw := ⟨r.variables,r.edges.map (row j)⟩

def rowComputes (j : ℕ) : Computes C.edgeEncoding E.Raw.factorEncoding (row j) := by
  let ports := (pairComputes (Wiring.firstComputes encodingNatBool encodingNatBool)
    (A.list₁ encodingNatBool (Wiring.secondComputes encodingNatBool encodingNatBool))).andThen
      (A.cons encodingNatBool)
  exact recode (pairComputes (constantComputes C.edgeEncoding encodingNatBool j) ports)
    id (fun _=>rfl) (fun _=>rfl)

def rawComputes (j : ℕ) : Computes C.encoding E.Raw.encoding (raw j) :=
  recode (pairComputes C.variablesComputes (C.edgesComputes.andThen
    (W.mapComputes C.edgeEncoding E.Raw.factorEncoding (row j) (rowComputes j))))
      id (fun _=>rfl) (fun _=>rfl)

variable {s : ℕ} {a : ℕ → ℕ} (j : Fin s)

theorem raw_valid (arity : a j.val=2) (r : P.Input) : O.Valid s a (raw j.val r.val) := by
  intro q hq
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hq
  have bounds := r.property.1 e he
  refine ⟨j.isLt,?_,?_⟩
  · simpa [row] using arity.symm
  · intro i hi
    simp only [row,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · exact bounds.1
    · exact bounds.2

def query (arity : a j.val=2) (r : P.Input) : O.Input s a :=
  ⟨raw j.val r.val,raw_valid j arity r⟩

def queryComputes (arity : a j.val=2) :
    Computes P.inputEncoding (O.inputEncoding s a) (query j arity) :=
  recode (rawComputes j.val) Subtype.val (fun _=>rfl) (fun _=>rfl)

section Semantics
variable {K : Type} [CommSemiring K]
variable (H : (i : Fin s) → Signature K (a i.val)) (f : Signature K 2)
variable (hj : (⟨a j.val,H j⟩ : AnySignature K)=⟨2,f⟩)

private theorem signature_apply {K : Type} {m n : ℕ}
    (f : Signature K m) (g : Signature K n)
    (h : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast (congrArg Sigma.fst h) i))=g x := by
  cases h
  rfl

include hj in
private theorem selected_apply (e : ℕ × ℕ) (x : ℕ → Bool) :
    O.rowValue H (row j.val e) x=f ![x e.1,x e.2] := by
  unfold StableHigherCurrentOrdinarySquare.rowValue row
  rw [dite_eq_left j.isLt]
  have h := signature_apply (H j) f hj
    ![x e.1,x e.2]
  convert h using 1
  congr 1
  funext k
  have ha : a j.val=2 := congrArg Sigma.fst hj
  have hk : k.val<2 := ha ▸ k.isLt
  have cases : k.val=0 ∨ k.val=1 := by omega
  rcases cases with hk | hk
  · have hc : Fin.cast (congrArg Sigma.fst hj) k=(0 : Fin 2) := Fin.ext hk
    simp [hk,hc,List.getD]
  · have hc : Fin.cast (congrArg Sigma.fst hj) k=(1 : Fin 2) := Fin.ext hk
    simp [hk,hc,List.getD]

theorem assignment_eq (r : C.Raw) (x : Fin r.variables→Bool) (i : ℕ) :
    O.extend x i=V.assignment r x i := by
  unfold StableHigherCurrentOrdinarySquare.extend BinaryCSPProgrammeValue.assignment
  by_cases hi : i<r.variables
  · rw [dite_eq_left hi,List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · rw [dite_eq_right hi,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]

theorem query_value (r : P.Input) :
    O.value H (query j (congrArg Sigma.fst hj) r).val=
      V.value (fun x y=>f ![x,y]) r.val := by
  apply Finset.sum_congr rfl
  intro x _
  simp only [StableHigherCurrentOrdinarySquare.weight,BinaryCSPProgrammeValue.weight,
    query,raw,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro e _
  rw [selected_apply j H f hj]
  simp only [assignment_eq]

end Semantics

section Bounds
local instance : Fintype Bool := Bool.fintype
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (H : (i : Fin s) → Signature K (a i.val))
abbrev Label := Bool ⊕ ((i : Fin s) × (Fin (a i.val)→Bool))
def base : Label (s:=s) (a:=a)→K
  | .inl b => if b then 1 else 0
  | .inr q => H q.1 q.2
omit [Algebra ℚ K] in
@[simp] theorem base_one : base H (.inl true)=1 := rfl
def coordinates (i : Label (s:=s) (a:=a)) : Fin d→ℚ := F.decode.symm (base H i)
def rowLabel (q : E.Factor) (x : ℕ→Bool) : Label (s:=s) (a:=a) :=
  if h : q.1<s then .inr ⟨⟨q.1,h⟩,fun k=>x (q.2.getD k.val 0)⟩ else .inl false

omit [Algebra ℚ K] in
theorem rowLabel_value (q : E.Factor) (x : ℕ→Bool) :
    base H (rowLabel q x)=O.rowValue H q x := by
  unfold rowLabel StableHigherCurrentOrdinarySquare.rowValue
  split_ifs <;> rfl

omit [Algebra ℚ K] in
theorem answer_bound (r : E.Raw) :
    ArithmeticSize.Bound (base H) (r.factors.length+r.variables) (O.value H r) := by
  classical
  let assignments := (Fintype.equivFin (Fin r.variables→Bool)).symm
  refine ⟨Fintype.card (Fin r.variables→Bool),fun t=>Fin.addCases
    (fun i : Fin r.factors.length=>rowLabel (r.factors.get i) (O.extend (assignments t)))
    (fun _ : Fin r.variables=>.inl true),?_,?_⟩
  · simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
  · simp only [Fin.prod_univ_add,Fin.addCases_left,Fin.addCases_right,base_one,
      Finset.prod_const_one,mul_one]
    rw [assignments.sum_comp (fun x=>∏i : Fin r.factors.length,
      base H (rowLabel (r.factors.get i) (O.extend x)))]
    apply Finset.sum_congr rfl
    intro x _
    simp only [rowLabel_value,StableHigherCurrentOrdinarySquare.weight]
    rw [←List.prod_ofFn]
    congr 1
    apply List.ext_getElem <;> simp

attribute [local instance] Classical.decEq

def targetOutput : PolynomialOutputBound (O.inputEncoding s a) F.encoding
    (fun r=>O.value H r.val) where
  bound := (BinaryInterpolation.RingFormulaMachine.widthPolynomial F (coordinates F H)).comp
    (2*Polynomial.X)
  length_le r := by
    classical
    have hb : ArithmeticSize.Bound (fun i=>F.decode (coordinates F H i))
        (r.val.factors.length+r.val.variables) (O.value H r.val) := by
      simpa only [coordinates,LinearEquiv.apply_symm_apply] using answer_bound H r.val
    have h := hb.encoded_length_le F (coordinates F H)
    rw [←BinaryInterpolation.RingFormulaMachine.width_eval] at h
    have hf := E.Raw.factor_count_le_length r.val
    have hv := E.Raw.variable_count_le_length r.val
    have hsum : r.val.factors.length+r.val.variables≤2*(E.Raw.encoding.encode r.val).length := by omega
    exact h.trans (by simpa only [Polynomial.eval_comp,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,
      StableHigherCurrentOrdinarySquareProgramme.inputEncoding] using
        natPolynomial_eval_mono (BinaryInterpolation.RingFormulaMachine.widthPolynomial F
          (coordinates F H)) hsum)

variable (f : Signature K 2)
variable (hj : (⟨a j.val,H j⟩ : AnySignature K)=⟨2,f⟩)

def controlled : LengthControlledOracleReduction P.inputEncoding F.encoding
    (O.inputEncoding s a) F.encoding
    (fun r=>V.value (fun x y=>f ![x,y]) r.val) (fun r=>O.value H r.val) :=
  controlledOneQueryOfEq (queryComputes j (congrArg Sigma.fst hj))
    (identityComputes F.encoding) (targetOutput F H)
    (fun r=>V.value (fun x y=>f ![x,y]) r.val) (fun r=>(query_value j H f hj r).symm)

variable (h00 : f ![false,false]≠0) (h01 : f ![false,true]≠0)
  (h10 : f ![true,false]≠0) (h11 : f ![true,true]=0)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (O.inputEncoding s a) F.encoding count (fun r=>O.value H r.val) :=
  Programme.compose (OrdinaryNegativeNANDSource.source F (fun x y=>f ![x,y])
    h00 h01 h10 h11 w) (controlled j F H f hj)

end Bounds
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNANDTable
end
