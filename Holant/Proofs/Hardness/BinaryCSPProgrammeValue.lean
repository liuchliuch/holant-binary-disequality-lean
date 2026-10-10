import Holant.Proofs.Hardness.BinaryCSPProgrammeRoots
import Holant.Complexity.OracleBatch.EncodingBounds
import Holant.Complexity.BinaryInterpolation.RingFormulaMachine

/-! Original-field answers for the literal unsigned binary CSP tape. The
declared variable domain is summed exactly, including unused variables. The
answer-byte bound is proved from that finite sum and the actual source codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeValue
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot
open BinaryCSPProgrammeCore
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
local instance : Fintype Bool := Bool.fintype

def assignment (r : Raw) (x : Fin r.variables→Bool) (i : ℕ) : Bool :=
  (List.ofFn x).getD i false

def weight {K : Type} [CommMonoid K] (f : Bool→Bool→K) (r : Raw)
    (x : Fin r.variables→Bool) : K :=
  (r.edges.map (fun e => f (assignment r x e.1) (assignment r x e.2))).prod

def value {K : Type} [CommSemiring K] (f : Bool→Bool→K) (r : Raw) : K :=
  ∑ x : Fin r.variables→Bool,weight f r x

@[simp] theorem empty_value {K : Type} [CommSemiring K] (f : Bool→Bool→K) (n : ℕ) :
    value f ⟨n,[],[]⟩=(2 : K)^n := by simp [value,weight,Fintype.card_fun]

theorem repeat_weight {K : Type} [CommMonoid K] (f : Bool→Bool→K) (r : Raw)
    (k : ℕ) (x : Fin r.variables→Bool) :
    weight f (BinaryCSPProgrammeRepeat.expand r k) x=(weight f r x)^(k+1) := by
  unfold weight BinaryCSPProgrammeRepeat.expand
  simp only [assignment]
  induction r.edges with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons,List.map_append,List.prod_append,List.map_replicate,
      List.prod_replicate,List.map_cons,List.prod_cons]
    rw [ih,mul_pow]

theorem repeat_value {K : Type} [CommSemiring K] (f : Bool→Bool→K) (r : Raw) (k : ℕ) :
    value f (BinaryCSPProgrammeRepeat.expand r k)=∑x : Fin r.variables→Bool,(weight f r x)^(k+1) := by
  apply Finset.sum_congr rfl
  intro x _
  exact repeat_weight f r k x

theorem counts_le_bytes (r : Raw) : r.variables+r.edges.length≤(encoding.encode r).length := by
  have h := OracleBatch.list_length_le (r.edges.map edgeEncoding.encode)
  rw [←OracleBatch.list_encode] at h
  simp only [List.length_map] at h
  change r.edges.length≤(edgesEncoding.encode r.edges).length at h
  change r.variables+r.edges.length≤(fieldsEncoding.encode r.fields).length
  simp only [fieldsEncoding,pairEncoding_length,Raw.fields,unary,UnaryBinary.unaryEncoding,
    List.length_replicate]
  omega

/-- Coefficient labels identify the four actual binary table entries; the
remaining fixed labels are used by the original-field arithmetic programme. -/
abbrev Label := Fin 6 ⊕ (Bool × Bool)

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b c : K) (f : Bool→Bool→K)

def literals : Fin 6→K := ![a,b,c,-1,1,2]
def base : Label→K
  | .inl i => literals a b c i
  | .inr bits => f bits.1 bits.2
def coordinates (i : Label) : Fin d→ℚ := F.decode.symm (base a b c f i)

@[simp] theorem decode_coordinates (i : Label) :
    F.decode (coordinates F a b c f i)=base a b c f i := by simp [coordinates]
@[simp] theorem base_unit : base a b c f (.inl 4)=1 := rfl
@[simp] theorem base_minus : base a b c f (.inl 3)= -1 := rfl
@[simp] theorem base_two : base a b c f (.inl 5)=2 := rfl

theorem answer_bound (r : Raw) :
    ArithmeticSize.Bound (base a b c f) (r.edges.length+r.variables) (value f r) := by
  classical
  let E := (Fintype.equivFin (Fin r.variables→Bool)).symm
  refine ⟨Fintype.card (Fin r.variables→Bool),fun t => Fin.addCases
    (fun i : Fin r.edges.length =>
      .inr (assignment r (E t) (r.edges.get i).1,assignment r (E t) (r.edges.get i).2))
    (fun _ : Fin r.variables => .inl 4),?_,?_⟩
  · simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
  · simp only [Fin.prod_univ_add,Fin.addCases_left,Fin.addCases_right,base_unit,
      Finset.prod_const_one,mul_one]
    rw [E.sum_comp (fun x => ∏ i : Fin r.edges.length,
      base a b c f (.inr (assignment r x (r.edges.get i).1,assignment r x (r.edges.get i).2)))]
    apply Finset.sum_congr rfl
    intro x _
    unfold weight
    rw [←List.prod_ofFn]
    congr 1
    apply List.ext_getElem <;> simp [base]

def targetOutput : PolynomialOutputBound encoding F.encoding (value f) where
  bound := BinaryInterpolation.RingFormulaMachine.widthPolynomial F (coordinates F a b c f)
  length_le r := by
    have hb : ArithmeticSize.Bound (fun i => F.decode (coordinates F a b c f i))
        (r.edges.length+r.variables) (value f r) := by
      simpa only [decode_coordinates] using answer_bound a b c f r
    have h := hb.encoded_length_le F (coordinates F a b c f)
    rw [←BinaryInterpolation.RingFormulaMachine.width_eval] at h
    exact h.trans (natPolynomial_eval_mono _ (by
      simpa [Nat.add_comm] using counts_le_bytes r))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeValue
