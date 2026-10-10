import Holant.Proofs.LinearProgramming.Foundation.Threshold

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Physical matrix compiler for a rational coordinate threshold 1/D. Counts and
indices are unary, D is canonical binary, all coefficients are canonical signed
integers. Every old row is read and padded, and the added row is tabulated by
real comparisons. This polynomial preprocessing subroutine is combined with
PositiveThreshold and the independently implemented exact LP solver.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ThresholdProgram
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec
noncomputable section

abbrev Query := Raw × (ℕ × ℕ)
def queryEncoding := pairEncoding encoding (pairEncoding UnaryBinary.unaryEncoding encodingNatBool)
def source : Computes queryEncoding encoding Prod.fst := Wiring.firstComputes _ _
def tail := Wiring.secondComputes encoding (pairEncoding UnaryBinary.unaryEncoding encodingNatBool)
def index : Computes queryEncoding UnaryBinary.unaryEncoding (fun q => q.2.1) :=
  tail.andThen (Wiring.firstComputes _ _)
def denominator : Computes queryEncoding encodingNatBool (fun q => q.2.2) :=
  tail.andThen (Wiring.secondComputes _ _)
def integerD : Computes queryEncoding IntegerArithmetic.encoding (fun q => (q.2.2:ℤ)) :=
  denominator.andThen RationalArithmetic.natCastComputes
def lastCoefficient : Computes queryEncoding IntegerArithmetic.encoding (fun q => 1-(q.2.2:ℤ)) :=
  congrComputes ((pairComputes (constantComputes queryEncoding IntegerArithmetic.encoding 1)
    ((pairComputes integerD (constantComputes queryEncoding IntegerArithmetic.encoding (-1))).andThen
      RationalArithmetic.integerMultiplicationComputes)).andThen RationalArithmetic.integerAdditionComputes)
    (fun q => by
      change (1 : ℤ) + (q.2.2 : ℤ) * (-1) = 1 - (q.2.2 : ℤ)
      ring)

def row (q : Query) : List ℤ :=
  (List.range q.1.dimension).map (fun k => if k=q.2.1 then (q.2.2:ℤ) else 0) ++ [1-(q.2.2:ℤ)]
def rawValue (q : Query) : Raw :=
  ⟨q.1.rowCount+1,q.1.dimension+1,q.1.rows.map (fun r => r++[0]) ++ [row q],q.1.rhs++[1]⟩

def rowComputes : Computes queryEncoding rowEncoding row := by
  let ctx := Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding
  let k := Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding
  let equal := (pairComputes k (ctx.andThen index)).andThen Parsing.unaryEqual
  let cell : Computes (pairEncoding queryEncoding UnaryBinary.unaryEncoding)
      IntegerArithmetic.encoding
      (fun x : Query × ℕ => if x.2=x.1.2.1 then (x.1.2.2 : ℤ) else 0) :=
    congrComputes (ifComputes equal (ctx.andThen integerD)
      (constantComputes (pairEncoding queryEncoding UnaryBinary.unaryEncoding)
        IntegerArithmetic.encoding 0)) (fun x => by
          change (if decide (x.2=x.1.2.1) = true then (x.1.2.2 : ℤ) else 0) = _
          simp only [decide_eq_true_eq])
  let front := WireLists.tabulate queryEncoding IntegerArithmetic.encoding (fun q => q.1.dimension)
    (source.andThen Parsing.dimension) (fun q k => if k=q.2.1 then (q.2.2:ℤ) else 0) cell
  let last := fixedListComputes queryEncoding IntegerArithmetic.encoding
    (fun q (_ : Unit) => 1-(q.2.2:ℤ)) (fun _ => lastCoefficient) [()]
  exact (pairComputes front last).andThen (WireLists.append IntegerArithmetic.encoding)

def rowsComputes : Computes queryEncoding rowsEncoding (fun q => (rawValue q).rows) := by
  let old := (source.andThen Parsing.rows).andThen
    (WireLists.mapComputes rowEncoding rowEncoding (fun r => r++[0])
      (appendComputes IntegerArithmetic.encoding [0]))
  let last := fixedListComputes queryEncoding rowEncoding (fun q (_ : Unit) => row q)
    (fun _ => rowComputes) [()]
  exact (pairComputes old last).andThen (WireLists.append rowEncoding)

def computes : Computes queryEncoding encoding rawValue :=
  recode (pairComputes ((source.andThen Parsing.rowCount).andThen WireLists.succComputes)
    (pairComputes ((source.andThen Parsing.dimension).andThen WireLists.succComputes)
      (pairComputes rowsComputes
        ((source.andThen Parsing.rhs).andThen (appendComputes IntegerArithmetic.encoding [1])))))
    id (fun _ => rfl) (fun _ => rfl)

theorem wellFormed (d : Input) (j D : ℕ) : (rawValue (d.val,j,D)).WellFormed := by
  rcases d.property with ⟨hm,hb,hw⟩
  refine ⟨by simp [rawValue,hm],by simp [rawValue,hb],?_⟩
  intro r hr
  simp only [rawValue,List.mem_append,List.mem_map,List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with ⟨old,ho,rfl⟩ | rfl
  · simp [rawValue,hw old ho]
  · simp [rawValue,row]

private theorem ofFn_getD {A : Type} (xs : List A) (z : A) {n : ℕ} (h : xs.length=n) :
    List.ofFn (fun i : Fin n => xs.getD i.val z) = xs := by
  apply List.ext_getElem <;> simp_all [List.getD_eq_getElem]

private theorem range_map {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

private theorem ofFn_lastCases {A : Type} {n : ℕ} (last : A) (f : Fin n → A) :
    List.ofFn (Fin.lastCases last f) = List.ofFn f ++ [last] := by
  rw [List.ofFn_succ']
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last,List.concat_eq_append]

theorem raw_exact (d : Input) (j : Fin d.val.dimension) (D : ℕ) :
    rawValue (d.val,j.val,D) = (Threshold.value d.val j D).val := by
  have hr : List.ofFn (fun i : Fin d.val.rowCount =>
      List.ofFn (fun k : Fin d.val.dimension => d.val.coefficient i k)) = d.val.rows := by
    have hrow (i : Fin d.val.rowCount) :
        (d.val.rows.getD i.val []).length=d.val.dimension := by
      have hi : i.val<d.val.rows.length := by simpa [d.property.1] using i.isLt
      rw [List.getD_eq_getElem _ _ hi]
      exact d.property.2.2 _ (List.getElem_mem hi)
    simp_rw [Raw.coefficient,ofFn_getD _ 0 (hrow _)]
    exact ofFn_getD _ [] d.property.1
  have hb := ofFn_getD d.val.rhs 0 d.property.2.1
  apply Raw.ext
  · rfl
  · rfl
  · change d.val.rows.map (fun r => r++[0]) ++ [row (d.val,j.val,D)] =
      List.ofFn (fun i => List.ofFn (Threshold.coefficients d.val j D i))
    rw [← hr,List.map_ofFn]
    change List.ofFn (fun i : Fin d.val.rowCount =>
      List.ofFn (d.val.coefficient i) ++ [0]) ++ [row (d.val,j.val,D)] = _
    rw [List.ofFn_succ' (fun i : Fin (d.val.rowCount+1) =>
      List.ofFn (Threshold.coefficients d.val j D i))]
    simp only [Threshold.coefficients,Fin.lastCases_castSucc,Fin.lastCases_last,
      List.concat_eq_append,ofFn_lastCases,row,range_map,Fin.ext_iff]
  · change d.val.rhs ++ [1] = List.ofFn (Fin.lastCases (1 : ℤ) d.val.constant)
    rw [ofFn_lastCases]
    exact congrArg (fun rows : List ℤ => rows++[1]) hb.symm

def value (q : Codec.CoordinateQuery × ℕ) : Input :=
  ⟨rawValue (q.1.1.val,q.1.2.val,q.2),wellFormed q.1.1 q.1.2.val q.2⟩
def validatedQueryEncoding := pairEncoding Codec.coordinateEncoding encodingNatBool
def prepare : Computes validatedQueryEncoding queryEncoding
    (fun q => (q.1.1.val,q.1.2.val,q.2)) := by
  let coordinate := Wiring.firstComputes Codec.coordinateEncoding encodingNatBool
  let raw : Computes Codec.coordinateEncoding encoding (fun c => c.1.val) :=
    recode (Wiring.firstComputes inputEncoding UnaryBinary.unaryEncoding)
      (fun c => (c.1,c.2.val)) (fun _ => rfl) (fun _ => rfl)
  let j : Computes Codec.coordinateEncoding UnaryBinary.unaryEncoding (fun c => c.2.val) :=
    recode (Wiring.secondComputes inputEncoding UnaryBinary.unaryEncoding)
      (fun c => (c.1,c.2.val)) (fun _ => rfl) (fun _ => rfl)
  exact pairComputes (coordinate.andThen raw) (pairComputes (coordinate.andThen j)
    (Wiring.secondComputes Codec.coordinateEncoding encodingNatBool))
def validatedComputes : Computes validatedQueryEncoding inputEncoding value :=
  recode (prepare.andThen computes) id (fun _ => rfl) (fun _ => rfl)

theorem exists_iff (d : Input) (j : Fin d.val.dimension) (D : ℕ) (hD : 1≤D) :
    (∃ y, Feasible (value (⟨d,j⟩,D)).val y) ↔
      ∃ x, Feasible d.val x ∧ 1/(D:ℚ)≤x j := by
  change (∃ y, Feasible (rawValue (d.val,j.val,D)) y) ↔ _
  rw [raw_exact d j D]
  exact Threshold.exists_iff d.val j D hD

theorem primitive_bound (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (Turing.initList computes.machine.computer (queryEncoding.encode q))) ≤
        (primitivePolynomial computes).eval (queryEncoding.encode q).length :=
  computes_primitive_cost computes q

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ThresholdProgram
