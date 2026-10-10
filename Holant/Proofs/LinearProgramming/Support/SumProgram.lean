import Holant.Proofs.LinearProgramming.Support.Infrastructure.Fold
import Holant.Proofs.LinearProgramming.Interface
import Holant.Algebraic.CommonDenominator
import Holant.OneHot.ArithmeticSize

/-!
Physical rational list summation with a polynomial bound on the same run.
The input is the literal framed rational list. Every reverse-fold state
retains that list, a physical unary cursor and the exact suffix sum.
The common denominator bound is derived from the original list bytes.
Even cursor-zero padding executes the eager candidate arithmetic; its full
step is retimed using the proved suffix-width invariant.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.SumProgram
open Computability Turing Holant.Algebraic Holant.OneHot Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 32768
set_option Elab.async false

private theorem foldr_sum (xs : List ℚ) : xs.foldr (· + ·) 0 = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldr_cons, List.sum_cons] using congrArg (x + ·) ih

noncomputable def sumPrepare : Computes Codec.pointEncoding
    (ReverseFold.inputEncoding rationalEncoding rationalEncoding) (fun xs => (xs, (0 : ℚ))) :=
  pairComputes (identityComputes Codec.pointEncoding)
    (constantComputes Codec.pointEncoding rationalEncoding 0)

noncomputable def sumFold : FiniteComputes
    (ReverseFold.inputEncoding rationalEncoding rationalEncoding) rationalEncoding
    (fun q => q.1.foldr (· + ·) q.2) :=
  ReverseFold.computes rationalEncoding rationalEncoding 0 (· + ·)
    (FiniteComputes.ofPoly RationalArithmetic.additionComputes)

noncomputable def sumRun : FiniteComputes Codec.pointEncoding rationalEncoding
    (fun xs => xs.foldr (· + ·) 0) :=
  (FiniteComputes.ofPoly sumPrepare).andThen sumFold

noncomputable def sumComputes : FiniteComputes Codec.pointEncoding rationalEncoding List.sum :=
  sumRun.congr foldr_sum


section
variable {A : Type} (f : A → ℚ) (one : A) (hOne : f one = 1)

include one hOne in
theorem sum_bound (xs : List ℚ) (b : ℕ)
    (hx : ∀ x∈xs,ArithmeticSize.Bound f b x) :
    ArithmeticSize.Bound f (b+xs.length) xs.sum := by
  induction xs with
  | nil => simpa using ArithmeticSize.Bound.zero (coeff := f) one b
  | cons x xs ih =>
    have ht := ih (fun y hy => hx y (by simp [hy]))
    have hh := (hx x (by simp)).mono one hOne (Nat.le_add_right b xs.length)
    simpa only [List.sum_cons,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using hh.add one hOne ht


end

theorem rational_height_from_bytes (a : ℚ) :
    rationalHeight a≤2^(rationalEncoding.encode a).length := by
  have hn : a.num.natAbs≤Equiv.intEquivNat a.num+1 := by
    cases h : a.num with
    | ofNat n => change n≤2*n+1; omega
    | negSucc n => change n+1≤(2*n+1)+1; omega
  have hl := Nat.left_le_pair (Equiv.intEquivNat a.num) a.den
  have hr := Nat.right_le_pair (Equiv.intEquivNat a.num) a.den
  have hb := Nat.lt_size_self (rationalCode a)
  change max a.num.natAbs a.den≤2^(encodeNat (rationalCode a)).length
  rw [encodeNat_length]
  unfold rationalCode at hb ⊢
  exact max_le (by omega) (by omega)

private theorem member_length {A : Type} (e : Encoding A Bool) (xs : List A)
    (a : A) (ha : a∈xs) : (e.encode a).length≤((framedListEncoding e).encode xs).length := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl | ht
    · simp only [framedListEncoding,framedListEncode,List.length_cons,List.length_append,frame_length]
      omega
    · have hh := ih ht
      simp only [framedListEncoding,framedListEncode,List.length_cons,List.length_append,frame_length] at hh ⊢
      omega

/-- A finite runtime table of B encoded bits has common denominator and
cleared-numerator sum with O(B²) bit lengths, including repeated literals. -/
theorem table_common_size (xs : List ℚ) :
    let B := (Codec.pointEncoding.encode xs).length
    max (familyNumeratorBound xs.get).size (commonDenominator xs.get).size≤B*B+2*B+1 := by
  let B := (Codec.pointEncoding.encode xs).length
  change max (familyNumeratorBound xs.get).size (commonDenominator xs.get).size≤B*B+2*B+1
  have hm : xs.length≤B := by
    have h := framedListEncoding_length_lower rationalEncoding xs
    change 2*xs.length+1≤B at h
    omega
  have he (i : Fin xs.length) : rationalHeight (xs.get i)≤2^B :=
    (rational_height_from_bytes _).trans (Nat.pow_le_pow_right (by decide)
      (member_length rationalEncoding xs _ (List.get_mem _ _)))
  have hn (i : Fin xs.length) : (xs.get i).num.natAbs≤2^B := (le_max_left _ _).trans (he i)
  have hd (i : Fin xs.length) : (xs.get i).den≤2^B := (le_max_right _ _).trans (he i)
  have hD : commonDenominator xs.get≤2^(B*B) := by
    calc
      commonDenominator xs.get≤∏ _i : Fin xs.length,2^B :=
        Finset.prod_le_prod (fun i _ => hd i)
      _ = 2^(B*xs.length) := by simp [← pow_mul]
      _ ≤ 2^(B*B) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left B hm)
  have hc (i : Fin xs.length) :
      (clearedNumerator xs.get i).natAbs≤2^B*commonDenominator xs.get := by
    simp only [clearedNumerator,Int.natAbs_mul,Int.natAbs_natCast]
    exact Nat.mul_le_mul (hn i) (Nat.div_le_self _ _)
  have hM : familyNumeratorBound xs.get≤2^(B*B+2*B) := by
    calc
      familyNumeratorBound xs.get≤∑ _i : Fin xs.length,2^B*commonDenominator xs.get :=
        Finset.sum_le_sum (fun i _ => hc i)
      _ = xs.length*(2^B*commonDenominator xs.get) := by simp
      _ ≤ 2^B*(2^B*2^(B*B)) := Nat.mul_le_mul
        (hm.trans (Nat.lt_two_pow_self (n := B)).le) (Nat.mul_le_mul_left _ hD)
      _ = 2^(B*B+2*B) := by rw [← pow_add,← pow_add]; congr 1; omega
  have hbD := Nat.size_le_size hD
  have hbM := Nat.size_le_size hM
  rw [Nat.size_pow] at hbD hbM
  exact max_le hbM (by omega)


def table (xs : List ℚ) := (1 : ℚ)::xs
def family (xs : List ℚ) : Fin (table xs).length → ℚ := (table xs).get
def unit (xs : List ℚ) : Fin (table xs).length := ⟨0,by simp [table]⟩
theorem unit_eq (xs : List ℚ) : family xs (unit xs)=1 := rfl

theorem member_bound (xs : List ℚ) (a : ℚ) (ha : a∈xs) : ArithmeticSize.Bound (family xs) 1 a := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_cons_of_mem 1 ha)
  simpa only [family,table,hi] using (ArithmeticSize.Bound.coefficient (coeff := family xs) i)

theorem suffix_bound (xs : List ℚ) (k : ℕ) :
    ArithmeticSize.Bound (family xs) (xs.length+1) (xs.drop k).sum := by
  have h := sum_bound (family xs) (unit xs) (unit_eq xs) (xs.drop k) 1
    (fun a ha => member_bound xs a (List.mem_of_mem_drop ha))
  exact h.mono (unit xs) (unit_eq xs) (by simp only [List.length_drop]; omega)

def tableOverhead : ℕ := 2*(rationalEncoding.encode 1).length+2
noncomputable def tablePolynomial : Polynomial ℕ := Polynomial.X+Polynomial.C tableOverhead
noncomputable def coefficientPolynomial : Polynomial ℕ := tablePolynomial*tablePolynomial+2*tablePolynomial+1
noncomputable def scalarPolynomial : Polynomial ℕ :=
  2*((Polynomial.X+1)+(Polynomial.X+1)*coefficientPolynomial+3)
noncomputable def widthPolynomial : Polynomial ℕ := 4*Polynomial.X+scalarPolynomial+2

theorem table_length (xs : List ℚ) : (Codec.pointEncoding.encode (table xs)).length=
    tablePolynomial.eval (Codec.pointEncoding.encode xs).length := by
  simp [table,tablePolynomial,tableOverhead,Codec.pointEncoding,framedListEncoding,
    framedListEncode,frame_length]
  omega

theorem suffix_bytes (xs : List ℚ) (k : ℕ) :
    (rationalEncoding.encode (xs.drop k).sum).length≤
      scalarPolynomial.eval (Codec.pointEncoding.encode xs).length := by
  obtain ⟨M,labels,hM,he⟩ := suffix_bound xs k
  have h := finiteFamily_sumProducts_length_le_exponential (family xs) labels hM
  rw [← he] at h
  have hc := table_common_size (table xs)
  rw [table_length] at hc
  have hn : xs.length≤(Codec.pointEncoding.encode xs).length := by
    have hlist := framedListEncoding_length_lower rationalEncoding xs
    change 2*xs.length+1≤(Codec.pointEncoding.encode xs).length at hlist
    omega
  have hm := Nat.mul_le_mul (Nat.add_le_add_right hn 1) hc
  simp only [scalarPolynomial,coefficientPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X]
  change max (familyNumeratorBound (family xs)).size (commonDenominator (family xs)).size≤_ at hc
  change (xs.length+1)*max (familyNumeratorBound (family xs)).size
    (commonDenominator (family xs)).size≤_ at hm
  omega

def encoding := ReverseFold.encoding rationalEncoding rationalEncoding
def initial (xs : List ℚ) := ReverseFold.start (xs,(0 : ℚ))
def next := ReverseFold.step (0 : ℚ) (· + ·)

theorem state_exact (xs : List ℚ) (k : ℕ) :
    (next^[k]) (initial xs)=(xs,xs.length-k,(xs.drop (xs.length-k)).sum) := by
  unfold next initial
  rw [ReverseFold.iterate_start]
  rfl

theorem state_bytes (xs : List ℚ) (k : ℕ) :
    (encoding.encode ((next^[k]) (initial xs))).length≤
      widthPolynomial.eval (Codec.pointEncoding.encode xs).length := by
  rw [state_exact]
  have hs := suffix_bytes xs (xs.length-k)
  have hn : xs.length≤(Codec.pointEncoding.encode xs).length := by
    have hlist := framedListEncoding_length_lower rationalEncoding xs
    change 2*xs.length+1≤(Codec.pointEncoding.encode xs).length at hlist
    omega
  simp only [encoding,ReverseFold.encoding,ReverseFold.tailEncoding,pairEncoding_length,
    UnaryBinary.unaryEncoding,List.length_replicate]
  simp only [widthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  change 2*(Codec.pointEncoding.encode xs).length+1+
    (2*(xs.length-k)+1+(rationalEncoding.encode (xs.drop (xs.length-k)).sum).length)≤_
  omega

noncomputable def timing : Timing sumComputes := by
  let prepare := pairComputes (identityComputes Codec.pointEncoding)
    (constantComputes Codec.pointEncoding rationalEncoding 0)
  let fold := Fold.after rationalEncoding rationalEncoding 0 (· + ·)
    (Timing.ofPoly prepare) (Timing.ofPoly RationalArithmetic.additionComputes)
    widthPolynomial state_bytes
  exact fold.congr (fun xs => by
    change xs.foldr (fun a b : ℚ => a+b) 0 = xs.sum
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa only [List.foldr_cons,List.sum_cons] using congrArg (x + ·) ih)


noncomputable def computes : Computes Codec.pointEncoding rationalEncoding List.sum := timing.computes
noncomputable def machine : Machine := computes.machine
noncomputable def time : Polynomial ℕ := computes.time
noncomputable def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial computes
noncomputable def storagePolynomial : Polynomial ℕ := Polynomial.X + primitivePolynomial

@[simp] theorem same_machine : computes.machine = sumComputes.machine := rfl
@[simp] theorem same_steps (xs : List ℚ) :
    (computes.outputs xs).steps = (sumComputes.outputs xs).steps := timing.computes_steps xs

theorem execution (xs : List ℚ) : StackProtocol.RunsExactly machine.computer.step
    (initList machine.computer (Codec.pointEncoding.encode xs))
    (haltList machine.computer (rationalEncoding.encode xs.sum)) (computes.outputs xs).steps :=
  (computes.outputs xs).evals_in_steps

theorem time_bound (xs : List ℚ) :
    (computes.outputs xs).steps ≤ time.eval (Codec.pointEncoding.encode xs).length :=
  (computes.outputs xs).steps_le_m

theorem primitive_bound (xs : List ℚ) :
    primitiveCost machine (computes.outputs xs).steps
      (some (initList machine.computer (Codec.pointEncoding.encode xs))) ≤
        primitivePolynomial.eval (Codec.pointEncoding.encode xs).length :=
  computes_primitive_cost computes xs

theorem prefix_storage (xs : List ℚ) (i : ℕ) (hi : i ≤ (computes.outputs xs).steps)
    (c : machine.Config) (hc : (fun p => p.bind machine.computer.step)^[i]
      (some (initList machine.computer (Codec.pointEncoding.encode xs))) = some c) :
    stackSize c.stk ≤ storagePolynomial.eval (Codec.pointEncoding.encode xs).length := by
  have hs := machine.run_size_le _ c i hc
  rw [machine.size_init] at hs
  have hcost := Nat.mul_le_mul_right machine.primitiveBudget
    (hi.trans (computes.outputs xs).steps_le_m)
  apply hs.trans
  simpa only [storagePolynomial, primitivePolynomial, FixedFieldMachines.primitivePolynomial,
    machine, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] using
      Nat.add_le_add_left hcost (Codec.pointEncoding.encode xs).length

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.SumProgram
