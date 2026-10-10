import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.Threshold
import Holant.Proofs.LinearProgramming.Foundation.ThresholdProgram

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
Physical p/q upper-threshold and exact-fixation integer matrix emitters.
p,q are binary words; only the original dimension is tabulated. No loop runs
p, q, a determinant, or a rational-grid magnitude many times. Original row
order, duplicate rows, zero rows and every RHS entry are retained.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators Codec
namespace ThresholdProgram
noncomputable section

abbrev Query := Raw × (ℕ × (ℕ × ℕ))
def fractionEncoding := pairEncoding encodingNatBool encodingNatBool
def indexFractionEncoding := pairEncoding UnaryBinary.unaryEncoding fractionEncoding
def encoding := pairEncoding Codec.encoding indexFractionEncoding
def source : Computes encoding Codec.encoding Prod.fst := Wiring.firstComputes _ _
def rest : Computes encoding indexFractionEncoding Prod.snd := Wiring.secondComputes _ _
def index : Computes encoding UnaryBinary.unaryEncoding (fun q : Query => q.2.1) :=
  rest.andThen (Wiring.firstComputes _ _)
def fraction : Computes encoding fractionEncoding (fun q : Query => q.2.2) :=
  rest.andThen (Wiring.secondComputes _ _)
def numerator : Computes encoding encodingNatBool (fun q : Query => q.2.2.1) :=
  fraction.andThen (Wiring.firstComputes _ _)
def denominator : Computes encoding encodingNatBool (fun q : Query => q.2.2.2) :=
  fraction.andThen (Wiring.secondComputes _ _)
def integerP : Computes encoding IntegerArithmetic.encoding (fun q : Query => (q.2.2.1:ℤ)) :=
  numerator.andThen RationalArithmetic.natCastComputes
def integerQ : Computes encoding IntegerArithmetic.encoding (fun q : Query => (q.2.2.2:ℤ)) :=
  denominator.andThen RationalArithmetic.natCastComputes

def front (q : Query) : List ℤ :=
  (List.range q.1.dimension).map (fun k => if k=q.2.1 then (q.2.2.2:ℤ) else 0)
def row (q : Query) : List ℤ := front q++[(q.2.2.1:ℤ)]
def rawValue (q : Query) : Raw :=
  ⟨q.1.rowCount+1,q.1.dimension+1,q.1.rows.map (fun r => r++[0])++[row q],
    q.1.rhs++[(q.2.2.1:ℤ)]⟩
def rawFixed (q : Query) : Raw :=
  ⟨q.1.rowCount+1,q.1.dimension,q.1.rows++[front q],q.1.rhs++[(q.2.2.1:ℤ)]⟩

def frontComputes : Computes encoding rowEncoding front := by
  let ctx := Wiring.firstComputes encoding UnaryBinary.unaryEncoding
  let k := Wiring.secondComputes encoding UnaryBinary.unaryEncoding
  let eq := (pairComputes k (ctx.andThen index)).andThen Parsing.unaryEqual
  let cell : Computes (pairEncoding encoding UnaryBinary.unaryEncoding)
      IntegerArithmetic.encoding
      (fun x : Query × ℕ => if x.2=x.1.2.1 then (x.1.2.2.2:ℤ) else 0) :=
    congrComputes (ifComputes eq (ctx.andThen integerQ)
      (constantComputes (pairEncoding encoding UnaryBinary.unaryEncoding) IntegerArithmetic.encoding 0))
      (fun x => by
        change (if decide (x.2=x.1.2.1)=true then (x.1.2.2.2:ℤ) else 0)=_
        simp only [decide_eq_true_eq])
  exact WireLists.tabulate encoding IntegerArithmetic.encoding (fun q : Query => q.1.dimension)
    (source.andThen Parsing.dimension) (fun q k => if k=q.2.1 then (q.2.2.2:ℤ) else 0) cell
def lastComputes : Computes encoding rowEncoding (fun q : Query => [(q.2.2.1:ℤ)]) :=
  fixedListComputes encoding IntegerArithmetic.encoding (fun q (_ : Unit) => (q.2.2.1:ℤ))
    (fun _ => integerP) [()]
def rowComputes : Computes encoding rowEncoding row :=
  (pairComputes frontComputes lastComputes).andThen (WireLists.append IntegerArithmetic.encoding)
def rhsComputes : Computes encoding rowEncoding (fun q : Query => q.1.rhs++[(q.2.2.1:ℤ)]) :=
  (pairComputes (source.andThen Parsing.rhs) lastComputes).andThen
    (WireLists.append IntegerArithmetic.encoding)
def rowsComputes : Computes encoding rowsEncoding (fun q : Query => (rawValue q).rows) := by
  let old := (source.andThen Parsing.rows).andThen
    (WireLists.mapComputes rowEncoding rowEncoding (fun r => r++[0])
      (appendComputes IntegerArithmetic.encoding [0]))
  let last := fixedListComputes encoding rowEncoding (fun q (_ : Unit) => row q) (fun _ => rowComputes) [()]
  exact (pairComputes old last).andThen (WireLists.append rowEncoding)
def fixedRowsComputes : Computes encoding rowsEncoding (fun q : Query => (rawFixed q).rows) :=
  (pairComputes (source.andThen Parsing.rows)
    (fixedListComputes encoding rowEncoding (fun q (_ : Unit) => front q) (fun _ => frontComputes) [()])).andThen
      (WireLists.append rowEncoding)
def computes : Computes encoding Codec.encoding rawValue :=
  recode (pairComputes ((source.andThen Parsing.rowCount).andThen WireLists.succComputes)
    (pairComputes ((source.andThen Parsing.dimension).andThen WireLists.succComputes)
      (pairComputes rowsComputes rhsComputes))) id (fun _ => rfl) (fun _ => rfl)
def fixedComputes : Computes encoding Codec.encoding rawFixed :=
  recode (pairComputes ((source.andThen Parsing.rowCount).andThen WireLists.succComputes)
    (pairComputes (source.andThen Parsing.dimension) (pairComputes fixedRowsComputes rhsComputes)))
      id (fun _ => rfl) (fun _ => rfl)

theorem wellFormed (d : Input) (j p q : ℕ) : (rawValue (d.val,j,p,q)).WellFormed := by
  rcases d.property with ⟨hm,hb,hw⟩
  refine ⟨by simp [rawValue,hm],by simp [rawValue,hb],?_⟩
  intro r hr
  simp only [rawValue,List.mem_append,List.mem_map,List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with ⟨old,ho,rfl⟩ | rfl
  · simp [rawValue,hw old ho]
  · simp [rawValue,row,front]
theorem fixedWellFormed (d : Input) (j p q : ℕ) : (rawFixed (d.val,j,p,q)).WellFormed := by
  rcases d.property with ⟨hm,hb,hw⟩
  refine ⟨by simp [rawFixed,hm],by simp [rawFixed,hb],?_⟩
  intro r hr
  simp only [rawFixed,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with ho | rfl
  · exact hw r ho
  · simp [rawFixed,front]

private theorem ofFn_getD {A : Type} (xs : List A) (z : A) {n : ℕ} (h : xs.length=n) :
    List.ofFn (fun i : Fin n => xs.getD i.val z)=xs := by
  apply List.ext_getElem <;> simp_all [List.getD_eq_getElem]
private theorem range_map {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp
private theorem ofFn_lastCases {A : Type} {n : ℕ} (last : A) (f : Fin n → A) :
    List.ofFn (Fin.lastCases last f)=List.ofFn f++[last] := by
  rw [List.ofFn_succ']
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last,List.concat_eq_append]
private theorem originalRows (d : Input) :
    List.ofFn (fun i : Fin d.val.rowCount => List.ofFn (d.val.coefficient i))=d.val.rows := by
  have hrow (i : Fin d.val.rowCount) : (d.val.rows.getD i.val []).length=d.val.dimension := by
    have hi : i.val<d.val.rows.length := by simpa [d.property.1] using i.isLt
    rw [List.getD_eq_getElem _ _ hi]
    exact d.property.2.2 _ (List.getElem_mem hi)
  change List.ofFn (fun i : Fin d.val.rowCount =>
    List.ofFn (fun k : Fin d.val.dimension => d.val.coefficient i k))=d.val.rows
  simp_rw [Raw.coefficient,ofFn_getD _ 0 (hrow _)]
  exact ofFn_getD _ [] d.property.1

theorem raw_exact (d : Input) (j : Fin d.val.dimension) (p q : ℕ) :
    rawValue (d.val,j.val,p,q)=(Threshold.value d.val j p q).val := by
  have hr := originalRows d
  have hb := ofFn_getD d.val.rhs 0 d.property.2.1
  apply Raw.ext
  · rfl
  · rfl
  · change d.val.rows.map (fun r => r++[0])++[row (d.val,j.val,p,q)]=
      List.ofFn (fun i => List.ofFn (Threshold.coefficients d.val j p q i))
    rw [← hr,List.map_ofFn]
    change List.ofFn (fun i : Fin d.val.rowCount =>
      List.ofFn (d.val.coefficient i)++[0])++[row (d.val,j.val,p,q)]=_
    rw [List.ofFn_succ' (fun i : Fin (d.val.rowCount+1) =>
      List.ofFn (Threshold.coefficients d.val j p q i))]
    simp only [Threshold.coefficients,Fin.lastCases_castSucc,Fin.lastCases_last,
      List.concat_eq_append,ofFn_lastCases,row,front,range_map,Fin.ext_iff]
  · change d.val.rhs++[(p:ℤ)]=List.ofFn (Fin.lastCases (p:ℤ) d.val.constant)
    rw [ofFn_lastCases]
    exact congrArg (fun rows : List ℤ => rows++[(p:ℤ)]) hb.symm
theorem fixed_exact (d : Input) (j : Fin d.val.dimension) (p q : ℕ) :
    rawFixed (d.val,j.val,p,q)=(Threshold.fixedValue d.val j p q).val := by
  have hr := originalRows d
  have hb := ofFn_getD d.val.rhs 0 d.property.2.1
  apply Raw.ext
  · rfl
  · rfl
  · change d.val.rows++[front (d.val,j.val,p,q)]=
      List.ofFn (fun i => List.ofFn (Threshold.fixedCoefficients d.val j q i))
    rw [List.ofFn_succ' (fun i : Fin (d.val.rowCount+1) =>
      List.ofFn (Threshold.fixedCoefficients d.val j q i))]
    simp only [Threshold.fixedCoefficients,Fin.lastCases_castSucc,Fin.lastCases_last,List.concat_eq_append]
    rw [hr]
    simp only [front,range_map,Fin.ext_iff]
  · change d.val.rhs++[(p:ℤ)]=List.ofFn (Fin.lastCases (p:ℤ) d.val.constant)
    rw [ofFn_lastCases]
    exact congrArg (fun rows : List ℤ => rows++[(p:ℤ)]) hb.symm

abbrev ValidatedQuery := CoordinateQuery × (ℕ × ℕ)
def validatedEncoding := pairEncoding coordinateEncoding fractionEncoding
def value (q : ValidatedQuery) : Input :=
  ⟨rawValue (q.1.1.val,q.1.2.val,q.2.1,q.2.2),wellFormed q.1.1 q.1.2.val q.2.1 q.2.2⟩
def fixedValue (q : ValidatedQuery) : Input :=
  ⟨rawFixed (q.1.1.val,q.1.2.val,q.2.1,q.2.2),fixedWellFormed q.1.1 q.1.2.val q.2.1 q.2.2⟩
def coordinateInput : Computes coordinateEncoding inputEncoding (fun c : CoordinateQuery => c.1) :=
  recode (Wiring.firstComputes inputEncoding UnaryBinary.unaryEncoding)
    (fun c => (c.1,c.2.val)) (fun _ => rfl) (fun _ => rfl)
def coordinateIndex : Computes coordinateEncoding UnaryBinary.unaryEncoding (fun c : CoordinateQuery => c.2.val) :=
  recode (Wiring.secondComputes inputEncoding UnaryBinary.unaryEncoding)
    (fun c => (c.1,c.2.val)) (fun _ => rfl) (fun _ => rfl)
def prepare : Computes validatedEncoding encoding
    (fun q : ValidatedQuery => (q.1.1.val,q.1.2.val,q.2.1,q.2.2)) := by
  let c := Wiring.firstComputes coordinateEncoding fractionEncoding
  let raw : Computes coordinateEncoding Codec.encoding (fun c : CoordinateQuery => c.1.val) :=
    recode coordinateInput id (fun _ => rfl) (fun _ => rfl)
  exact pairComputes (c.andThen raw) (pairComputes (c.andThen coordinateIndex)
    (Wiring.secondComputes coordinateEncoding fractionEncoding))
def validatedComputes : Computes validatedEncoding inputEncoding value :=
  recode (prepare.andThen computes) id (fun _ => rfl) (fun _ => rfl)
def validatedFixedComputes : Computes validatedEncoding inputEncoding fixedValue :=
  recode (prepare.andThen fixedComputes) id (fun _ => rfl) (fun _ => rfl)

theorem exists_iff (c : CoordinateQuery) (p q : ℕ) (hq : 0<q) :
    (∃ y, Feasible (value (c,p,q)).val y) ↔ ∃ x, Feasible c.1.val x ∧ x c.2≤(p:ℚ)/q := by
  change (∃ y, Feasible (rawValue (c.1.val,c.2.val,p,q)) y) ↔ _
  rw [raw_exact c.1 c.2 p q]
  exact Threshold.exists_iff c.1.val c.2 p q hq
theorem fixed_feasible (c : CoordinateQuery) (p q : ℕ) (hq : 0<q)
    (x : Fin c.1.val.dimension → ℚ) :
    Feasible (fixedValue (c,p,q)).val x ↔ Feasible c.1.val x ∧ x c.2=(p:ℚ)/q := by
  change Feasible (rawFixed (c.1.val,c.2.val,p,q)) x ↔ _
  have hrows := congrArg Raw.rows (fixed_exact c.1 c.2 p q)
  have hrhs := congrArg Raw.rhs (fixed_exact c.1 c.2 p q)
  have hc (i : Fin (c.1.val.rowCount+1)) (j : Fin c.1.val.dimension) :
      (rawFixed (c.1.val,c.2.val,p,q)).coefficient i j =
        (Threshold.fixedValue c.1.val c.2 p q).val.coefficient i j := by
    unfold Raw.coefficient
    rw [hrows]
  have hb (i : Fin (c.1.val.rowCount+1)) :
      (rawFixed (c.1.val,c.2.val,p,q)).constant i =
        (Threshold.fixedValue c.1.val c.2 p q).val.constant i := by
    unfold Raw.constant
    rw [hrhs]
  have he := Threshold.fixed_feasible c.1.val c.2 p q hq x
  change ((∀ i : Fin (c.1.val.rowCount+1), ∑ j : Fin c.1.val.dimension,
      ((Threshold.fixedValue c.1.val c.2 p q).val.coefficient i j : ℚ)*x j =
        (Threshold.fixedValue c.1.val c.2 p q).val.constant i) ∧
      ∀ j : Fin c.1.val.dimension, 0≤x j ∧ x j≤1) ↔ _ at he
  change ((∀ i : Fin (c.1.val.rowCount+1), ∑ j : Fin c.1.val.dimension,
      ((rawFixed (c.1.val,c.2.val,p,q)).coefficient i j : ℚ)*x j =
        (rawFixed (c.1.val,c.2.val,p,q)).constant i) ∧
      ∀ j : Fin c.1.val.dimension, 0≤x j ∧ x j≤1) ↔ _
  simpa only [hc,hb] using he

theorem output_bound (q : ValidatedQuery) : (inputEncoding.encode (value q)).length≤
    validatedComputes.outputBound.bound.eval (validatedEncoding.encode q).length :=
  validatedComputes.outputBound.length_le q
theorem primitive_bound (q : ValidatedQuery) :
    primitiveCost validatedComputes.machine (validatedComputes.outputs q).steps
      (some (initList validatedComputes.machine.computer (validatedEncoding.encode q)))≤
      (primitivePolynomial validatedComputes).eval (validatedEncoding.encode q).length :=
  computes_primitive_cost validatedComputes q

end
end ThresholdProgram
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
