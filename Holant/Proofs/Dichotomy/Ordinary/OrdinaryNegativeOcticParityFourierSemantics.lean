import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticParityFourier

/-! Exact ordered-row semantics of the positive Fourier block. The shared
constant is pinned by its literal row; every H/T factor is evaluated at the
actual addresses. No parity oracle is present. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityFourierSemantics
open Holant Holant.Tractable
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open OrdinaryNegativeOcticParityFourier
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option Elab.async false

/-- Addresses0..2 are the logical ports;3..52 are the25 actual private pairs;
53 is the shared constant. The extension outside the block is irrelevant. -/
def assignment (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool) (c : Bool) (i : ℕ) : Bool :=
  if h : i<3 then x ⟨i,h⟩ else if h : i<53 then
    let v : Fin 25 := ⟨(i-3)/2,by omega⟩
    if (i-3)%2=0 then (bits v).1 else (bits v).2
  else c

@[simp] theorem assignment_logical (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool)
    (c : Bool) (i : Fin 3) : assignment x bits c i.val=x i := by
  simp [assignment,i.isLt]

@[simp] theorem assignment_center (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool)
    (c : Bool) (i : Fin 25) : assignment x bits c (center i)=(bits i).1 := by
  have h0 : ¬center i<3 := by unfold center; omega
  have h1 : center i<53 := by unfold center; omega
  have h2 : (center i-3)/2=i.val := by unfold center; omega
  have h3 : (center i-3)%2=0 := by unfold center; omega
  simp [assignment,h0,h1,h2,h3]

@[simp] theorem assignment_phase (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool)
    (c : Bool) (i : Fin 25) : assignment x bits c (phase i)=(bits i).2 := by
  have h0 : ¬phase i<3 := by unfold phase; omega
  have h1 : phase i<53 := by unfold phase; omega
  have h2 : (phase i-3)/2=i.val := by unfold phase; omega
  have h3 : (phase i-3)%2≠0 := by unfold phase; omega
  simp [assignment,h0,h1,h2,h3]

@[simp] theorem assignment_constant (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool)
    (c : Bool) : assignment x bits c constant=c := by simp [assignment,constant]

variable {K : Type*} [CommRing K]
def rowValue (z : K) (w : ℕ → Bool) (r : Factor) : K :=
  if r.1=0 then character (w (r.2.getD 0 0)) (w (r.2.getD 1 0))
  else if r.1=1 then z^(w (r.2.getD 0 0)).toNat
  else if w (r.2.getD 0 0) then 0 else 1

def weight (z : K) (w : ℕ → Bool) (rows : List Factor) : K :=
  (rows.map (rowValue z w)).prod

private theorem filter_product {α : Type*} (p : α → Bool) (f : α → K) (xs : List α) :
    ((xs.filter p).map f).prod=(xs.map (fun i=>if p i then f i else 1)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [h,ih]

private theorem selected_inputs (z : K) (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool)
    (v : Fin 25) :
    ((((List.finRange 3).filter (fun j=>I.mask (term v) j)).map
      (fun j=>(0,[center v,j.val]) : Fin 3 → Factor)).map
        (rowValue z (assignment x bits false))).prod=
      inputProduct (term v) (bits v).1 x := by
  simp only [List.map_map,Function.comp_def]
  have h : (fun j : Fin 3=>rowValue z (assignment x bits false) (0,[center v,j.val]))=
      fun j=>character (bits v).1 (x j) := by
    funext j
    simp [rowValue]
  rw [h,filter_product]
  rw [←List.ofFn_eq_map,List.prod_ofFn]
  rfl

theorem termRows_value (z : K) (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool)
    (v : Fin 25) :
    weight z (assignment x bits false) (termRows v)=
      termWeight z (term v) x (bits v).1 (bits v).2 := by
  unfold weight termRows
  simp only [List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil]
  rw [selected_inputs]
  have pad : ((if pairMask (term v) then [(0,[center v,constant])] else []).map
      (rowValue z (assignment x bits false))).prod=1 := by
    cases pairMask (term v) <;> simp [rowValue,character]
  rw [pad]
  simp [rowValue,termWeight,mul_assoc]

/-- The literal pin0 factor kills every assignment with the shared constant1. -/
theorem weight_true_zero (z : K) (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool) :
    weight z (assignment x bits true) factors=0 := by
  simp [weight,factors,List.map_append,List.prod_append,rowValue]

private theorem product_flatMap {α : Type*} (xs : List α) (f : α → List K) :
    (xs.flatMap f).prod=(xs.map (fun x=>(f x).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,List.prod_append,List.map_cons,List.prod_cons,ih]

theorem weight_false (z : K) (x : Fin 3 → Bool) (bits : Fin 25 → Bool×Bool) :
    weight z (assignment x bits false) factors=blockWeight z x bits := by
  unfold weight factors
  simp only [List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil]
  have pin : rowValue z (assignment x bits false) (2,[constant])=1 := by simp [rowValue]
  rw [pin,mul_one,mul_one]
  rw [List.map_flatMap,product_flatMap]
  change ((List.finRange 25).map (fun v=>weight z (assignment x bits false) (termRows v))).prod=_
  simp_rw [termRows_value]
  rw [←List.ofFn_eq_map,List.prod_ofFn]
  rfl

/-- Summing precisely the25 private bit pairs and the one pinned constant
has the expected fixed scale. The statement uses the literal row evaluator. -/
theorem rows_cubic (z : K) (hfour : z^4= -1) (x : Fin 3 → Bool) :
    (∑bits : Fin 25 → Bool×Bool,∑c : Bool,weight z (assignment x bits c) factors)=
      2^25*OrdinaryNegativeCubicCore.cubic x := by
  simp_rw [Fintype.sum_bool,weight_true_zero,weight_false,zero_add]
  exact block_cubic z hfour x
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeOcticParityFourierSemantics
end
