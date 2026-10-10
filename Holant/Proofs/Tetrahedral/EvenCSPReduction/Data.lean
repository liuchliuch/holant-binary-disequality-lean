import Holant.Complexity.ClosedNetworkEncoding
import Holant.Complexity.GraphPreprocessing.UnaryBinary
import Holant.BoundaryAction
import Mathlib.Algebra.BigOperators.Ring.Finset


namespace Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open Holant Holant.Complexity Computability
open scoped BigOperators

abbrev Factor := ℕ × List ℕ

structure Raw where
  «variables» : ℕ
  factors : List Factor
  deriving DecidableEq

namespace Raw

def factorEncoding : Encoding Factor Bool :=
  framedProductEncoding encodingNatBool (framedListEncoding encodingNatBool)

def encoding : Encoding Raw Bool where
  encode r := (framedProductEncoding GraphPreprocessing.UnaryBinary.unaryEncoding
    (framedListEncoding factorEncoding)).encode (r.variables,r.factors)
  decode bits := ((framedProductEncoding GraphPreprocessing.UnaryBinary.unaryEncoding
    (framedListEncoding factorEncoding)).decode bits).map (fun p => ⟨p.1,p.2⟩)
  decode_encode r := by simp

abbrev Ports (r : Raw) := Σ v : Fin r.factors.length,
  Fin (r.factors.get v).2.length

/-- The actual variable address in the original factor's ordered port. -/
def address (r : Raw) (p : r.Ports) : ℕ := (r.factors.get p.1).2.get p.2

/-- Stable original factor/port order; equal variable addresses remain
different occurrences. This list is computed, never supplied as input. -/
def portList (r : Raw) : List r.Ports :=
  (List.finRange r.factors.length).flatMap (fun v =>
    (List.finRange (r.factors.get v).2.length).map (fun j => ⟨v,j⟩))

def occurrences (r : Raw) (i : ℕ) : List r.Ports :=
  r.portList.filter (fun p => r.address p == i)

def degree (r : Raw) (i : ℕ) : ℕ := (r.occurrences i).length

def Valid (s : ℕ) (a : ℕ → ℕ) (r : Raw) : Prop :=
  (∀ v : Fin r.factors.length,
    (r.factors.get v).1 < s ∧ (r.factors.get v).2.length=a (r.factors.get v).1) ∧
  (∀ p : r.Ports, r.address p < r.variables) ∧
  (∀ i < r.variables, Even (r.degree i))

instance validDecidable (s : ℕ) (a : ℕ → ℕ) (r : Raw) :
    Decidable (r.Valid s a) := by
  unfold Valid
  infer_instance

abbrev Input (s : ℕ) (a : ℕ → ℕ) := {r : Raw // r.Valid s a}

def validatedEncoding (s : ℕ) (a : ℕ → ℕ) : Encoding (Input s a) Bool where
  encode r := encoding.encode r.val
  decode bits := (encoding.decode bits).bind (fun r =>
    if h : r.Valid s a then some ⟨r,h⟩ else none)
  decode_encode r := by simp [r.property]

theorem variable_count_le_length (r : Raw) : r.variables ≤ (encoding.encode r).length := by
  change r.variables ≤ ((framedProductEncoding GraphPreprocessing.UnaryBinary.unaryEncoding
    (framedListEncoding factorEncoding)).encode (r.variables,r.factors)).length
  rw [framedProductEncoding_length]
  simp only [GraphPreprocessing.UnaryBinary.unaryEncoding,List.length_replicate]
  try dsimp only at *
  omega

private theorem payload_sum_le {α : Type} (e : Encoding α Bool) (w : α → ℕ)
    (hw : ∀x,w x≤(e.encode x).length) (xs : List α) :
    (xs.map w).sum≤((framedListEncoding e).encode xs).length := by
  induction xs with
  | nil => simp [framedListEncoding,framedListEncode]
  | cons x xs ih =>
    have hx := hw x
    simp only [List.map_cons,List.sum_cons,framedListEncoding,framedListEncode,
      List.length_cons,List.length_append,Holant.Algebraic.frame_length]
    change w x+(xs.map w).sum≤_ 
    change (xs.map w).sum≤(framedListEncode e xs).length at ih
    omega

theorem ports_card (r : Raw) :
    Fintype.card r.Ports=(r.factors.map (fun row => row.2.length)).sum := by
  simp only [Ports,Fintype.card_sigma,Fintype.card_fin]
  rw [←List.sum_ofFn]
  congr 1
  simpa only [List.get_eq_getElem] using
    (List.ofFn_getElem_eq_map r.factors (fun row : Factor => row.2.length))

theorem factor_count_le_length (r : Raw) : r.factors.length≤(encoding.encode r).length := by
  have h := framedListEncoding_length_lower factorEncoding r.factors
  change r.factors.length≤((framedProductEncoding GraphPreprocessing.UnaryBinary.unaryEncoding
    (framedListEncoding factorEncoding)).encode (r.variables,r.factors)).length
  rw [framedProductEncoding_length]
  try dsimp only at *
  omega

theorem port_count_le_length (r : Raw) : Fintype.card r.Ports≤(encoding.encode r).length := by
  have hrow (row : Factor) : row.2.length≤(factorEncoding.encode row).length := by
    have h := framedListEncoding_length_lower encodingNatBool row.2
    change row.2.length≤((framedProductEncoding encodingNatBool
      (framedListEncoding encodingNatBool)).encode row).length
    rw [framedProductEncoding_length]
    omega
  have h := payload_sum_le factorEncoding (fun row : Factor => row.2.length) hrow r.factors
  rw [ports_card]
  change (r.factors.map (fun row => row.2.length)).sum≤
    ((framedProductEncoding GraphPreprocessing.UnaryBinary.unaryEncoding
      (framedListEncoding factorEncoding)).encode (r.variables,r.factors)).length
  rw [framedProductEncoding_length]
  try dsimp only at *
  omega

theorem portList_complete (r : Raw) (p : r.Ports) : p ∈ r.portList := by
  apply List.mem_flatMap.mpr
  refine ⟨p.1,List.mem_finRange _,?_⟩
  exact List.mem_map.mpr ⟨p.2,List.mem_finRange _,rfl⟩

theorem occurrences_mem (r : Raw) (i : ℕ) (p : r.Ports) :
    p ∈ r.occurrences i ↔ r.address p=i := by
  simp [occurrences,r.portList_complete p]

theorem degree_zero_iff (r : Raw) (i : ℕ) :
    r.degree i=0 ↔ ∀p : r.Ports,r.address p≠i := by
  simp [degree,List.length_eq_zero_iff,List.eq_nil_iff_forall_not_mem,occurrences_mem]

def route {s : ℕ} {a : ℕ → ℕ} (r : Input s a) (p : r.val.Ports) : Fin r.val.variables :=
  ⟨r.val.address p,r.property.2.1 p⟩

def label {s : ℕ} {a : ℕ → ℕ} (r : Input s a) (v : Fin r.val.factors.length) : Fin s :=
  ⟨(r.val.factors.get v).1,(r.property.1 v).1⟩

def portCast {s : ℕ} {a : ℕ → ℕ} (r : Input s a)
    (v : Fin r.val.factors.length) (j : Fin (a (label r v).val)) : r.val.Ports :=
  ⟨v,Fin.cast (r.property.1 v).2.symm j⟩

section Value
variable {K : Type*} [CommSemiring K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))

def factorWeight (r : Input s a) (z : r.val.Ports → Bool) : K :=
  ∏v : Fin r.val.factors.length,G (label r v) (fun j => z (portCast r v j))

def value (r : Input s a) : K :=
  ∑x : Fin r.val.variables → Bool,factorWeight G r (fun p => x (route r p))

/-- The equality constraint at one actual declared variable. An empty
fiber sums its two Boolean choices and contributes exactly two. -/
def variableWeight (r : Input s a) (z : r.val.Ports → Bool)
    (i : Fin r.val.variables) : K :=
  ∑b : Bool,∏p : r.val.Ports,
    if route r p=i then Signature.equality (z p) b else 1

def incidenceValue (r : Input s a) : K :=
  ∑z : r.val.Ports → Bool,factorWeight G r z * ∏i,variableWeight r z i

end Value
end Raw
end Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
