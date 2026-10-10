import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.Completion.PhaseMatrix
import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.PhaseOneProgram

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Physical full phase-I matrix emission, including every zero block and RHS.
The source is the unchanged original integer Codec.Input. All list appends,
unit-row comparisons, length counts, 2^L scale bits and framing are charged.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.PhaseCompiler
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec
noncomputable section

abbrev Query := Raw × ℕ
def queryEncoding := pairEncoding encoding UnaryBinary.unaryEncoding
def source : Computes queryEncoding encoding Prod.fst := Wiring.firstComputes _ _
def index : Computes queryEncoding UnaryBinary.unaryEncoding Prod.snd := Wiring.secondComputes _ _
def zeroN := (source.andThen Parsing.dimension).andThen (WireLists.replicate IntegerArithmetic.encoding 0)
def zeroM := (source.andThen Parsing.rowCount).andThen (WireLists.replicate IntegerArithmetic.encoding 0)
def oldRow := AccessPrograms.get rowEncoding [] (source.andThen Parsing.rows) index
def scale := (source.andThen PhaseOneProgram.naturalScale).andThen RationalArithmetic.natCastComputes
def negativeScale := scale.andThen Comparison.integerNegate

def unitWord (q : Query) (a : ℤ) : List ℤ :=
  (List.range q.1.rowCount).map (fun j => if j=q.2 then a else 0)

private def unitComputes (a : Query → ℤ) (w : Computes queryEncoding IntegerArithmetic.encoding a) :
    Computes queryEncoding rowEncoding (fun q => unitWord q (a q)) := by
  let ctx := Wiring.firstComputes queryEncoding UnaryBinary.unaryEncoding
  let j := Wiring.secondComputes queryEncoding UnaryBinary.unaryEncoding
  let equal := (pairComputes j (ctx.andThen index)).andThen Parsing.unaryEqual
  let cell : Computes (pairEncoding queryEncoding UnaryBinary.unaryEncoding)
      IntegerArithmetic.encoding
      (fun x : Query × ℕ => if x.2=x.1.2 then a x.1 else 0) :=
    congrComputes (ifComputes equal (ctx.andThen w)
      (constantComputes (pairEncoding queryEncoding UnaryBinary.unaryEncoding)
        IntegerArithmetic.encoding 0)) (fun x => by
          change (if decide (x.2=x.1.2) = true then a x.1 else 0) = _
          simp only [decide_eq_true_eq])
  exact WireLists.tabulate queryEncoding IntegerArithmetic.encoding (fun q => q.1.rowCount)
    (source.andThen Parsing.rowCount) (fun q j => if j=q.2 then a q else 0) cell

def unitPositive := unitComputes (fun q => (PhaseOne.scale q.1 : ℤ)) scale
def unitNegative := unitComputes (fun q => -(PhaseOne.scale q.1 : ℤ)) negativeScale
def unitOne := unitComputes (fun _ => 1) (constantComputes queryEncoding IntegerArithmetic.encoding 1)

def listBlocks (x u v r s : List ℤ) (t : ℤ) : List ℤ := x++u++v++r++s++[t]
private def append {f g : Query → List ℤ} (a : Computes queryEncoding rowEncoding f)
    (b : Computes queryEncoding rowEncoding g) : Computes queryEncoding rowEncoding (fun q => f q++g q) :=
  (pairComputes a b).andThen (WireLists.append IntegerArithmetic.encoding)

private def blocksComputes {x u v r s : Query → List ℤ}
    (wx : Computes queryEncoding rowEncoding x) (wu : Computes queryEncoding rowEncoding u)
    (wv : Computes queryEncoding rowEncoding v) (wr : Computes queryEncoding rowEncoding r)
    (ws : Computes queryEncoding rowEncoding s) (t : ℤ) :
    Computes queryEncoding rowEncoding (fun q => listBlocks (x q) (u q) (v q) (r q) (s q) t) :=
  (append (append (append (append wx wu) wv) wr) ws).andThen
    (appendComputes IntegerArithmetic.encoding [t])

def balanceRow (q : Query) : List ℤ := listBlocks (q.1.rows.getD q.2 [])
  (unitWord q (-(PhaseOne.scale q.1 : ℤ))) (unitWord q (PhaseOne.scale q.1 : ℤ))
  (List.replicate q.1.rowCount 0) (List.replicate q.1.rowCount 0) 0
def positiveRow (q : Query) : List ℤ := listBlocks (List.replicate q.1.dimension 0)
  (unitWord q 1) (List.replicate q.1.rowCount 0) (unitWord q 1) (List.replicate q.1.rowCount 0) (-1)
def negativeRow (q : Query) : List ℤ := listBlocks (List.replicate q.1.dimension 0)
  (List.replicate q.1.rowCount 0) (unitWord q 1) (List.replicate q.1.rowCount 0) (unitWord q 1) (-1)

def balanceComputes : Computes queryEncoding rowEncoding balanceRow :=
  blocksComputes oldRow unitNegative unitPositive zeroM zeroM 0
def positiveComputes : Computes queryEncoding rowEncoding positiveRow :=
  blocksComputes zeroN unitOne zeroM unitOne zeroM (-1)
def negativeComputes : Computes queryEncoding rowEncoding negativeRow :=
  blocksComputes zeroN zeroM unitOne zeroM unitOne (-1)

def rawValue (d : Raw) : Raw := ⟨PhaseMatrix.height d,PhaseMatrix.width d,
  (List.range d.rowCount).map (fun i => balanceRow (d,i)) ++
    (List.range d.rowCount).map (fun i => positiveRow (d,i)) ++
    (List.range d.rowCount).map (fun i => negativeRow (d,i)),
  d.rhs++List.replicate d.rowCount 0++List.replicate d.rowCount 0⟩

def rawComputes : Computes encoding encoding rawValue := by
  let a := WireLists.tabulate encoding rowEncoding Raw.rowCount Parsing.rowCount
    (fun d i => balanceRow (d,i)) balanceComputes
  let b := WireLists.tabulate encoding rowEncoding Raw.rowCount Parsing.rowCount
    (fun d i => positiveRow (d,i)) positiveComputes
  let c := WireLists.tabulate encoding rowEncoding Raw.rowCount Parsing.rowCount
    (fun d i => negativeRow (d,i)) negativeComputes
  let ab := (pairComputes a b).andThen (WireLists.append rowEncoding)
  let rows := (pairComputes ab c).andThen (WireLists.append rowEncoding)
  let z := Parsing.rowCount.andThen (WireLists.replicate IntegerArithmetic.encoding 0)
  let rhs := (pairComputes ((pairComputes Parsing.rhs z).andThen (WireLists.append IntegerArithmetic.encoding)) z).andThen
    (WireLists.append IntegerArithmetic.encoding)
  let twice := (pairComputes Parsing.rowCount Parsing.rowCount).andThen AccessPrograms.unaryAdd
  let count := (pairComputes twice Parsing.rowCount).andThen AccessPrograms.unaryAdd
  let n1 := (pairComputes Parsing.dimension Parsing.rowCount).andThen AccessPrograms.unaryAdd
  let n2 := (pairComputes n1 Parsing.rowCount).andThen AccessPrograms.unaryAdd
  let n3 := (pairComputes n2 Parsing.rowCount).andThen AccessPrograms.unaryAdd
  let n4 := (pairComputes n3 Parsing.rowCount).andThen AccessPrograms.unaryAdd
  exact recode (pairComputes count (pairComputes (n4.andThen WireLists.succComputes)
    (pairComputes rows rhs))) id (fun _ => rfl) (fun _ => rfl)

private theorem range_ofFn {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

private theorem ofFn_getD {α : Type} (xs : List α) (z : α) (n : ℕ) (hn : xs.length=n) :
    List.ofFn (fun i : Fin n => xs.getD i.val z)=xs := by
  apply List.ext_getElem <;> simp_all [List.getD_eq_getElem]

private theorem blocks_ofFn {n m : ℕ} (x : Fin n → ℤ) (u v r s : Fin m → ℤ) (t : ℤ) :
    List.ofFn (PhaseMatrix.blocks x u v r s t) =
      listBlocks (List.ofFn x) (List.ofFn u) (List.ofFn v) (List.ofFn r) (List.ofFn s) t := by
  unfold PhaseMatrix.blocks
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc,Fin.snoc_last,List.ofFn_fin_append,
    List.concat_eq_append,listBlocks,List.append_assoc]

private theorem unit_ofFn (d : Raw) (i : Fin d.rowCount) (a : ℤ) :
    unitWord (d,i.val) a = List.ofFn (PhaseMatrix.unit d.rowCount i a) := by
  rw [unitWord,range_ofFn]
  apply congrArg List.ofFn
  funext j
  dsimp only [PhaseMatrix.unit]
  by_cases h : j=i
  · subst j
    simp
  · have hv : j.val≠i.val := fun he => h (Fin.ext he)
    simp only [hv,h,if_false]

theorem raw_exact (d : Input) : rawValue d.val=(PhaseMatrix.value d.val).val := by
  have hr (i : Fin d.val.rowCount) :
      List.ofFn (d.val.coefficient i)=d.val.rows.getD i.val [] := by
    have hi : i.val<d.val.rows.length := by simpa [d.property.1] using i.isLt
    have hw : (d.val.rows.getD i.val []).length=d.val.dimension := by
      rw [List.getD_eq_getElem _ _ hi]
      exact d.property.2.2 _ (List.getElem_mem hi)
    exact ofFn_getD _ 0 _ hw
  have hb := ofFn_getD d.val.rhs 0 _ d.property.2.1
  have hb' : List.ofFn d.val.constant=d.val.rhs := hb
  have ha (i : Fin d.val.rowCount) :
      balanceRow (d.val,i.val)=List.ofFn (PhaseMatrix.balance d.val i) := by
    change balanceRow (d.val,i.val)=List.ofFn
      (PhaseMatrix.blocks (d.val.coefficient i)
        (PhaseMatrix.unit d.val.rowCount i (-(PhaseOne.scale d.val : ℤ)))
        (PhaseMatrix.unit d.val.rowCount i (PhaseOne.scale d.val : ℤ))
        (fun _ : Fin d.val.rowCount => (0 : ℤ)) (fun _ : Fin d.val.rowCount => (0 : ℤ)) 0)
    rw [blocks_ofFn]
    simp only [balanceRow,hr,← unit_ofFn,List.ofFn_const]
  have hu (i : Fin d.val.rowCount) :
      positiveRow (d.val,i.val)=List.ofFn (PhaseMatrix.positive d.val i) := by
    change positiveRow (d.val,i.val)=List.ofFn
      (PhaseMatrix.blocks (fun _ : Fin d.val.dimension => (0 : ℤ))
        (PhaseMatrix.unit d.val.rowCount i 1) (fun _ : Fin d.val.rowCount => (0 : ℤ))
        (PhaseMatrix.unit d.val.rowCount i 1) (fun _ : Fin d.val.rowCount => (0 : ℤ)) (-1))
    rw [blocks_ofFn]
    simp only [positiveRow,← unit_ofFn,List.ofFn_const]
  have hv (i : Fin d.val.rowCount) :
      negativeRow (d.val,i.val)=List.ofFn (PhaseMatrix.negative d.val i) := by
    change negativeRow (d.val,i.val)=List.ofFn
      (PhaseMatrix.blocks (fun _ : Fin d.val.dimension => (0 : ℤ))
        (fun _ : Fin d.val.rowCount => (0 : ℤ)) (PhaseMatrix.unit d.val.rowCount i 1)
        (fun _ : Fin d.val.rowCount => (0 : ℤ)) (PhaseMatrix.unit d.val.rowCount i 1) (-1))
    rw [blocks_ofFn]
    simp only [negativeRow,← unit_ofFn,List.ofFn_const]
  have hcoeff : List.ofFn (PhaseMatrix.coefficients d.val)=
      List.ofFn (PhaseMatrix.balance d.val) ++ List.ofFn (PhaseMatrix.positive d.val) ++
        List.ofFn (PhaseMatrix.negative d.val) := by
    change List.ofFn (Fin.append
      (Fin.append (PhaseMatrix.balance d.val) (PhaseMatrix.positive d.val))
      (PhaseMatrix.negative d.val))=_
    rw [List.ofFn_fin_append,List.ofFn_fin_append]
  apply Raw.ext
  · rfl
  · rfl
  · change (List.range d.val.rowCount).map (fun i => balanceRow (d.val,i)) ++
      (List.range d.val.rowCount).map (fun i => positiveRow (d.val,i)) ++
      (List.range d.val.rowCount).map (fun i => negativeRow (d.val,i)) =
        List.ofFn (fun i => List.ofFn (PhaseMatrix.coefficients d.val i))
    rw [range_ofFn,range_ofFn,range_ofFn,
      List.ofFn_comp' (PhaseMatrix.coefficients d.val) List.ofFn,hcoeff]
    simp only [List.map_append,
      List.map_ofFn,Function.comp_def,← ha,← hu,← hv,List.append_assoc]
  · change d.val.rhs++List.replicate d.val.rowCount 0++List.replicate d.val.rowCount 0 =
      List.ofFn (PhaseMatrix.constants d.val)
    change d.val.rhs++List.replicate d.val.rowCount 0++List.replicate d.val.rowCount 0 =
      List.ofFn (Fin.append (Fin.append d.val.constant (fun _ : Fin d.val.rowCount => (0 : ℤ)))
        (fun _ : Fin d.val.rowCount => (0 : ℤ)))
    simp only [List.ofFn_fin_append,List.ofFn_const,
      hb',List.append_assoc]

def value (d : Input) : Input := PhaseMatrix.value d.val
def computes : Computes inputEncoding inputEncoding value :=
  recode rawComputes Subtype.val (fun _ => rfl)
    (fun d => congrArg encoding.encode (raw_exact d))

theorem correct (d : Input) (y : Fin (PhaseMatrix.width d.val) → ℚ) :
    Codec.Feasible (value d).val y ↔ PhaseOne.Feasible d.val (PhaseMatrix.point d.val y) :=
  PhaseMatrix.feasible_point d.val y

theorem output_bound (d : Input) : (inputEncoding.encode (value d)).length ≤
    computes.outputBound.bound.eval (inputEncoding.encode d).length := computes.outputBound.length_le d

theorem primitive_bound (d : Input) :
    primitiveCost computes.machine (computes.outputs d).steps
      (some (initList computes.machine.computer (inputEncoding.encode d))) ≤
      (primitivePolynomial computes).eval (inputEncoding.encode d).length := computes_primitive_cost computes d

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion.PhaseCompiler
