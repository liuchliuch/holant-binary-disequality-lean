import Holant.Proofs.Hardness.BinaryIsingRaw
import Holant.Proofs.Hardness.BinaryIsingWeights
import Holant.Proofs.Hardness.BinaryCSPProgrammeValue
import Holant.Proofs.Hardness.EOBinaryPlaneRaw

/-! Exact positive-exponent Ising query semantics on the literal graph codec.
The finite coefficient family and answer-length bound come from the actual
three interaction rows, not from an assumed short-answer oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingQuery
open Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot BinaryCSPProgrammeCore
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

abbrev Query := Raw×ℕ
abbrev queryEncoding := pairEncoding encoding unary

def comparisons (r : Raw) (z : Fin (r.variables+1)→Bool) : List Bool :=
  r.edges.flatMap fun e=>
    [decide (EOBinaryPlaneRaw.read z (e.1+1)=z 0),
     decide (EOBinaryPlaneRaw.read z (e.2+1)=z 0),
     decide (!(EOBinaryPlaneRaw.read z (e.1+1))=EOBinaryPlaneRaw.read z (e.2+1))]

def repeatedComparisons (a : Query) (z : Fin (a.1.variables+1)→Bool) : List Bool :=
  (comparisons a.1 z).flatMap (List.replicate (a.2+1))

def coefficient {K : Type*} (p q : K) (b : Bool) : K := if b then p else q

def value {K : Type*} [CommSemiring K] (p q : K) (a : Query) : K :=
  ∑z : Fin (a.1.variables+1)→Bool,((repeatedComparisons a z).map (coefficient p q)).prod

@[simp] theorem comparisons_length (r : Raw) (z : Fin (r.variables+1)→Bool) :
    (comparisons r z).length=r.edges.length*3 := by
  simp [comparisons,List.length_flatMap,List.sum_replicate]
@[simp] theorem repeated_length (a : Query) (z : Fin (a.1.variables+1)→Bool) :
    (repeatedComparisons a z).length=a.1.edges.length*3*(a.2+1) := by
  simp [repeatedComparisons,List.length_flatMap,List.sum_replicate]

def left (r : Raw) (hr : r.WellFormed) (i : Fin r.edges.length) : Fin r.variables :=
  ⟨(r.edges.get i).1,(hr.1 _ (List.get_mem _ _)).1⟩
def right (r : Raw) (hr : r.WellFormed) (i : Fin r.edges.length) : Fin r.variables :=
  ⟨(r.edges.get i).2,(hr.1 _ (List.get_mem _ _)).2⟩

theorem weight_eq {K : Type*} [Field K] (p q : K) (r : Raw) (k : ℕ)
    (z : Fin (r.variables+1)→Bool) :
    ((repeatedComparisons (r,k) z).map (coefficient p q)).prod=
      (r.edges.map (fun e=>BinaryIsingWeights.block p q (z 0)
        (EOBinaryPlaneRaw.read z (e.1+1)) (EOBinaryPlaneRaw.read z (e.2+1)))).prod^(k+1) := by
  have hrep (bs : List Bool) : ((bs.flatMap (List.replicate (k+1))).map (coefficient p q)).prod=
      (bs.map (coefficient p q)).prod^(k+1) := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.flatMap_cons,List.map_append,List.prod_append,List.map_replicate,
        List.prod_replicate,List.map_cons,List.prod_cons]
      rw [ih,mul_pow]
  rw [repeatedComparisons,hrep]
  congr 1
  unfold comparisons
  induction r.edges with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons,List.map_append,List.prod_append,List.map_cons,List.prod_cons,
      List.map_nil,List.prod_nil,mul_one]
    rw [ih]
    cases ha : z 0 <;> cases hx : EOBinaryPlaneRaw.read z (e.1+1) <;>
      cases hy : EOBinaryPlaneRaw.read z (e.2+1) <;>
      simp [coefficient,BinaryIsingWeights.block,BinaryIsingWeights.interaction,mul_assoc]

theorem value_eq_partition {K : Type*} [Field K] (p q : K) (r : Raw)
    (hr : r.WellFormed) (k : ℕ) :
    value p q (r,k)=BinaryIsingWeights.partition p q (left r hr) (right r hr) (k+1) := by
  unfold value BinaryIsingWeights.partition
  apply Finset.sum_congr rfl
  intro z _
  rw [weight_eq,Finset.prod_pow]
  congr 1
  rw [←List.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn]
    have hleft := EOBinaryPlaneRaw.read_at z (left r hr ⟨i,by simpa using hi⟩).succ
    have hright := EOBinaryPlaneRaw.read_at z (right r hr ⟨i,by simpa using hi⟩).succ
    simpa only [left,right,Fin.val_succ,List.get_eq_getElem] using
      congrArg₂ (BinaryIsingWeights.block p q (z 0)) hleft hright

abbrev Label := Fin 7⊕Bool

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (p q : K)

def base : Label→K
  | .inl i => ![p,q,p^2*q,q/p,1,-1,2] i
  | .inr b => coefficient p q b
def coordinates (i : Label) : Fin d→ℚ := F.decode.symm (base p q i)
@[simp] theorem decode_coordinates (i : Label) : F.decode (coordinates F p q i)=base p q i := by
  simp [coordinates]
omit [Algebra ℚ K] in
@[simp] theorem base_unit : base p q (.inl 4)=1 := rfl
omit [Algebra ℚ K] in
@[simp] theorem base_minus : base p q (.inl 5)= -1 := rfl
omit [Algebra ℚ K] in
@[simp] theorem base_two : base p q (.inl 6)=2 := rfl
omit [Algebra ℚ K] in
@[simp] theorem base_scalar : base p q (.inl 2)=p^2*q := rfl
omit [Algebra ℚ K] in
@[simp] theorem base_ratio : base p q (.inl 3)=q/p := rfl

def budget (a : Query) : ℕ := a.1.edges.length*3*(a.2+1)+(a.1.variables+1)

omit [Algebra ℚ K] in
theorem answer_bound (a : Query) : ArithmeticSize.Bound (base p q) (budget a) (value p q a) := by
  classical
  unfold budget
  let E := (Fintype.equivFin (Fin (a.1.variables+1)→Bool)).symm
  refine ⟨Fintype.card (Fin (a.1.variables+1)→Bool),fun t=>Fin.addCases
    (fun i : Fin (a.1.edges.length*3*(a.2+1))=>
      .inr ((repeatedComparisons a (E t)).get ⟨i.val,by rw [repeated_length]; exact i.isLt⟩))
    (fun _ : Fin (a.1.variables+1)=>.inl 4),?_,?_⟩
  · simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
  · simp only [Fin.prod_univ_add,Fin.addCases_left,Fin.addCases_right,base_unit,
      Finset.prod_const_one,mul_one]
    rw [E.sum_comp (fun z=>∏i : Fin (a.1.edges.length*3*(a.2+1)),
      base p q (.inr ((repeatedComparisons a z).get ⟨i.val,by rw [repeated_length]; exact i.isLt⟩)))]
    unfold value
    apply Finset.sum_congr rfl
    intro z _
    rw [←List.prod_ofFn]
    congr 1
    apply List.ext_getElem <;> simp [base]

def sizePolynomial : Polynomial ℕ := 3*Polynomial.X*(Polynomial.X+1)+Polynomial.X+1

theorem budget_le (a : Query) : budget a≤sizePolynomial.eval (queryEncoding.encode a).length := by
  have hr := BinaryCSPProgrammeValue.counts_le_bytes a.1
  have hl : (queryEncoding.encode a).length=2*(encoding.encode a.1).length+1+a.2 := by
    simp [queryEncoding,unary,UnaryBinary.unaryEncoding]
  have hn : a.1.edges.length≤(queryEncoding.encode a).length := by omega
  have hk : a.2≤(queryEncoding.encode a).length := by omega
  have hm : a.1.variables≤(queryEncoding.encode a).length := by omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_right 3 hn) (Nat.add_le_add_right hk 1)
  simp only [budget,sizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  nlinarith

def targetOutput : PolynomialOutputBound queryEncoding F.encoding (value p q) where
  bound := (BinaryInterpolation.RingFormulaMachine.widthPolynomial F (coordinates F p q)).comp sizePolynomial
  length_le a := by
    have hb : ArithmeticSize.Bound (fun i=>F.decode (coordinates F p q i)) (budget a) (value p q a) := by
      simpa only [decode_coordinates] using answer_bound p q a
    have h := hb.encoded_length_le F (coordinates F p q)
    rw [←BinaryInterpolation.RingFormulaMachine.width_eval] at h
    exact h.trans (by
      simpa only [Polynomial.eval_comp] using natPolynomial_eval_mono
        (BinaryInterpolation.RingFormulaMachine.widthPolynomial F (coordinates F p q)) (budget_le a))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingQuery
