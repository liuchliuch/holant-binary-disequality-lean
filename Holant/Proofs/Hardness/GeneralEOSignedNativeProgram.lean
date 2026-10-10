import Holant.Proofs.Hardness.GeneralEOSignedNativeQuery
import Holant.Proofs.Hardness.GeneralEOSignedParityUnused

/-! The signed query writer computes the actual component traversal, selects
its fixed palette row, and serializes all compressed scopes. No row signs,
component identifiers or running-time certificates occur in the input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeProgram
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot.StackProgram.GraphLabelEncoding
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
namespace R
export GeneralEOSignedNativeRaw (Input Query inputEncoding queryEncoding parsed rowPairing
  endpoint endpoint_native endpointComputes parsedComputes)
end R
namespace Q
export GeneralEOSignedNativeQuery (count enumeration label signs rowSigns rowLabel rowScopes query)
end Q
namespace Pr
export GeneralEOSignedParityProgram (inputEncoding tabulate scopes signs scopesComputes signListComputes twiceComputes)
end Pr
namespace C
export FixedGadgetSubstitution.Compiler
  (sourceComputes sourceLabel labelRecodeComputes edgeCountComputes vertexCountComputes)
end C
namespace W
export Holant.LocalDrafts.Tractability.AffineMachine.WireLists (getD flatten)
end W
namespace F
export GeneralEOPairedCSPFamilyRaw (encoding labelsEncoding addressesEncoding labelEncoding)
end F
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
abbrev unary := UnaryBinary.unaryEncoding
variable {s : ℕ} {arity : ℕ → ℕ}
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))

def scopeAt (x : R.Query (s:=s) (arity:=arity)) (k : ℕ) : ℕ :=
  (Pr.scopes (R.parsed P x.1)).getD (R.endpoint x k).1 0

def signAt (x : R.Query (s:=s) (arity:=arity)) (k : ℕ) : Bool :=
  Bool.xor ((Pr.signs (R.parsed P x.1)).getD (R.endpoint x k).1 false) (R.endpoint x k).2

def scopeFor (i : Fin s) (x : R.Query (s:=s) (arity:=arity)) (j : Fin (P i).count) : ℕ :=
  scopeAt P x ((P i).ports (j,false)).val

def signsFor (i : Fin s) (x : R.Query (s:=s) (arity:=arity)) : Fin (P i).count → Bool :=
  fun j => signAt P x ((P i).ports (j,false)).val

theorem finRange_getD {A : Type} {n : ℕ} (f : Fin n → A) (i : Fin n) (d : A) :
    ((List.finRange n).map f).getD i.val d=f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

theorem scope_native (x : R.Query (s:=s) (arity:=arity))
    (k : Fin (arity (x.1.val.vertices.get x.2).1)) :
    scopeAt P x k.val = (GeneralEOSignedParityComponents.scope (R.parsed P x.1).2
      (GeneralEOSignedNativeParity.port (x.1.val.shape x.1.property) x.2 k).1).val := by
  simp only [scopeAt,R.endpoint_native]
  exact finRange_getD _ _ _

theorem sign_native (x : R.Query (s:=s) (arity:=arity))
    (k : Fin (arity (x.1.val.vertices.get x.2).1)) :
    signAt P x k.val = Bool.xor
      (GeneralEOSignedParityComponents.signs (R.parsed P x.1).2
        (GeneralEOSignedNativeParity.port (x.1.val.shape x.1.property) x.2 k).1)
      (GeneralEOSignedNativeParity.port (x.1.val.shape x.1.property) x.2 k).2 := by
  simp only [signAt,R.endpoint_native]
  rw [Pr.signs,finRange_getD]

theorem signsFor_eq (x : R.Query (s:=s) (arity:=arity)) :
    signsFor P (C.sourceLabel s 1 arity x) x = Q.rowSigns P x.1 x.2 := by
  funext j
  exact sign_native P x _

theorem scopeFor_eq (x : R.Query (s:=s) (arity:=arity)) :
    List.ofFn (scopeFor P (C.sourceLabel s 1 arity x) x)=Q.rowScopes P x.1 x.2 := by
  congr 1
  funext j
  exact scope_native P x _

def scopeAtComputes (k : ℕ) : Computes (R.queryEncoding (s:=s) (arity:=arity)) unary
    (fun x => scopeAt P x k) :=
  (pairComputes (((C.sourceComputes s 1 arity).andThen (R.parsedComputes P)).andThen Pr.scopesComputes)
    ((R.endpointComputes (s:=s) (arity:=arity) k).andThen (Wiring.firstComputes unary encodingBoolBool))).andThen
    (W.getD unary 0)

def xorComputes : Computes (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p => Bool.xor p.1 p.2) :=
  FiniteRecode.computes (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p => Bool.xor p.1 p.2) 5
    (fun p => by rcases p with ⟨a,b⟩; cases a <;> cases b <;> decide)

def signAtComputes (k : ℕ) : Computes (R.queryEncoding (s:=s) (arity:=arity)) encodingBoolBool
    (fun x => signAt P x k) :=
  (pairComputes
    ((pairComputes (((C.sourceComputes s 1 arity).andThen (R.parsedComputes P)).andThen Pr.signListComputes)
      ((R.endpointComputes (s:=s) (arity:=arity) k).andThen (Wiring.firstComputes unary encodingBoolBool))).andThen
        (W.getD encodingBoolBool false))
    ((R.endpointComputes (s:=s) (arity:=arity) k).andThen (Wiring.secondComputes unary encodingBoolBool))).andThen
      xorComputes

/-- A fixed Boolean word is literally concatenated from its computed bits. -/
def wordComputes {A : Type} {n : ℕ} (ea : Encoding A Bool) (f : A → Fin n → Bool)
    (w : ∀j,Computes ea encodingBoolBool (fun a => f a j)) : Computes ea (assignmentEncoding n) f :=
  recode (fixedConcatComputes ea (fun a j => [f a j])
    (fun j => recode (w j) id (fun _ => rfl) (fun _ => rfl)) (List.finRange n))
    id (fun _ => rfl) (fun a => by
      change (List.finRange n).flatMap (fun j => [f a j])=List.ofFn (f a)
      rw [←List.map_eq_flatMap]
      apply List.ext_getElem <;> simp)

def signsForComputes (i : Fin s) : Computes (R.queryEncoding (s:=s) (arity:=arity))
    (assignmentEncoding (P i).count) (signsFor P i) :=
  wordComputes (R.queryEncoding (s:=s) (arity:=arity)) (signsFor P i)
    (fun j => signAtComputes P ((P i).ports (j,false)).val)

def rowLabelForComputes (i : Fin s) : Computes (R.queryEncoding (s:=s) (arity:=arity))
    (F.labelEncoding (Q.count P)) (fun x => Q.enumeration P ⟨i,signsFor P i x⟩) :=
  (signsForComputes P i).andThen
    (FiniteRecode.computes (assignmentEncoding (P i).count) (F.labelEncoding (Q.count P))
      (fun b => Q.enumeration P ⟨i,b⟩) (P i).count (fun b => by simp))

def rowLabelComputes : Computes (R.queryEncoding (s:=s) (arity:=arity))
    (F.labelEncoding (Q.count P)) (fun x => Q.rowLabel P x.1 x.2) :=
  congrComputes (chooseComputes (R.queryEncoding (s:=s) (arity:=arity)) (F.labelEncoding (Q.count P)) s
    (C.sourceLabel s 1 arity) (fun x i => Q.enumeration P ⟨i,signsFor P i x⟩)
    (C.labelRecodeComputes s 1 arity unary Fin.val) (rowLabelForComputes P))
    (fun x => by rw [signsFor_eq]; rfl)

def rowScopesForComputes (i : Fin s) : Computes (R.queryEncoding (s:=s) (arity:=arity))
    F.addressesEncoding (fun x => List.ofFn (scopeFor P i x)) :=
  congrComputes (fixedListComputes (R.queryEncoding (s:=s) (arity:=arity)) encodingNatBool
    (scopeFor P i) (fun j => (scopeAtComputes P ((P i).ports (j,false)).val).andThen UnaryBinary.computes)
    (List.finRange (P i).count)) (fun x => by apply List.ext_getElem <;> simp)

def rowScopesComputes : Computes (R.queryEncoding (s:=s) (arity:=arity)) F.addressesEncoding
    (fun x => Q.rowScopes P x.1 x.2) :=
  congrComputes (chooseComputes (R.queryEncoding (s:=s) (arity:=arity)) F.addressesEncoding s
    (C.sourceLabel s 1 arity) (fun x i => List.ofFn (scopeFor P i x))
    (C.labelRecodeComputes s 1 arity unary Fin.val) (rowScopesForComputes P)) (scopeFor_eq P)

def labelsComputes : Computes (R.inputEncoding (s:=s) (arity:=arity)) (F.labelsEncoding (Q.count P))
    (fun r => List.ofFn (Q.rowLabel P r)) :=
  congrComputes (Pr.tabulate (R.inputEncoding (s:=s) (arity:=arity)) (F.labelEncoding (Q.count P))
    (fun r => r.val.vertices.length) (C.vertexCountComputes s 1 arity) (Q.rowLabel P)
    (rowLabelComputes P)) (fun r => by apply List.ext_getElem <;> simp)

def addressesComputes : Computes (R.inputEncoding (s:=s) (arity:=arity)) F.addressesEncoding
    (fun r => (List.finRange r.val.vertices.length).flatMap (Q.rowScopes P r)) :=
  congrComputes ((Pr.tabulate (R.inputEncoding (s:=s) (arity:=arity)) F.addressesEncoding
    (fun r => r.val.vertices.length) (C.vertexCountComputes s 1 arity) (Q.rowScopes P)
    (rowScopesComputes P)).andThen (W.flatten encodingNatBool))
    (fun _ => by simp [List.flatMap_def])

/-- The complete literal signed compressed-CSP query writer. -/
def queryComputes : Computes (R.inputEncoding (s:=s) (arity:=arity)) (F.encoding (Q.count P)) (Q.query P) :=
  recode (pairComputes ((C.edgeCountComputes s 1 arity).andThen Pr.twiceComputes)
    (pairComputes (labelsComputes P) (addressesComputes P))) id (fun _ => rfl) (fun _ => rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeProgram
