import Holant.Proofs.Tractability.ProductMachine.Bytecode
import Holant.Proofs.Tractability.ProductMachine.SymbolicElimination
import Holant.Proofs.Tractability.ProductMachine.PivotScan


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.Tractability.ProductMachine.Isolated

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open Templates (Record recordEncoding)
open Holant.OneHot.StackProgram
open ProductElimination (LabelledFactor)

def atom (b : Bool) (r : Record) : Expr ℕ :=
  if r.1 = 1 then
    if r.2.1 = 0 then .literal (if b then r.2.2.2.1 else r.2.2.1) else .one
  else if r.1 = 2 then
    if r.2.1 = 0 then
      if r.2.2.1 = 0 then (if r.2.2.2.1 = 0 then .one else .zero) else .zero
    else if r.2.2.1 = 0 then .zero else .one
  else .one

def keep (r : Record) : Bool :=
  if r.1 = 1 then r.2.1 != 0
  else if r.1 = 2 then (r.2.1 != 0) && (r.2.2.1 != 0)
  else true

def tail (fs : List Record) : List Record :=
  (fs.filter keep).map (Rewrite.record (0, false))

def head (fs : List Record) (b : Bool) := Expr.product (fs.map (atom b))
def multiplier (fs : List Record) := Expr.add (head fs false) (head fs true)

noncomputable def atomEmits (b : Bool) : Bytecode.Emits recordEncoding encodingNatBool (atom b) := by
  let one := Bytecode.constant recordEncoding encodingNatBool .one
  let zero := Bytecode.constant recordEncoding encodingNatBool .zero
  let coeff := (Rewrite.getComputes (if b then 3 else 2)).andThen (Bytecode.literal encodingNatBool)
  let unary := ifComputes (PivotScan.equal 1 0) coeff one
  let link := ifComputes (PivotScan.equal 1 0)
    (ifComputes (PivotScan.equal 2 0) (ifComputes (PivotScan.equal 3 0) one zero) zero)
    (ifComputes (PivotScan.equal 2 0) zero one)
  exact congrComputes (ifComputes (PivotScan.equal 0 1) unary
    (ifComputes (PivotScan.equal 0 2) link one))
    (fun r => by
      cases b <;> simp [atom, Rewrite.get]
        <;> split_ifs <;> simp_all)

noncomputable def keepComputes : Computes recordEncoding encodingBoolBool keep := by
  let left := (PivotScan.equal 1 0).andThen Rewrite.negComputes
  let right := (PivotScan.equal 2 0).andThen Rewrite.negComputes
  exact congrComputes (ifComputes (PivotScan.equal 0 1) left
    (ifComputes (PivotScan.equal 0 2)
      ((pairComputes left right).andThen (Rewrite.boolPairComputes (fun p => p.1 && p.2)))
      (constantComputes recordEncoding encodingBoolBool true)))
    (fun r => by simp [keep, Rewrite.get, bne, Bool.beq_eq_decide_eq])

noncomputable def tailComputes :
    Computes (framedListEncoding recordEncoding) (framedListEncoding recordEncoding) tail := by
  let rewrite := (pairComputes (constantComputes recordEncoding Rewrite.pivotEncoding (0, false))
    (identityComputes recordEncoding)).andThen Rewrite.computes
  let each := ifComputes keepComputes (rewrite.andThen (entryComputes recordEncoding))
    (constantComputes recordEncoding Frame.wordEncoding [])
  refine recode (joinComputes (Bytecode.flatMap recordEncoding _ each)
    (constantComputes (framedListEncoding recordEncoding) Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro fs
  have h : fs.flatMap (fun r => if keep r then entry recordEncoding (Rewrite.record (0, false) r) else []) =
      entries recordEncoding (tail fs) := by
    induction fs with
    | nil => rfl
    | cons r rs ih => cases hk : keep r <;> simp [tail, entries, hk, ih]
  change fs.flatMap (fun r => if keep r then entry recordEncoding (Rewrite.record (0, false) r) else []) ++ [false] = _
  rw [h]
  simpa only [framedListEncoding, framedListEncode, List.append_nil] using entries_append_encode recordEncoding (tail fs) []

noncomputable def headEmits (b : Bool) :
    Bytecode.Emits (framedListEncoding recordEncoding) encodingNatBool (fun fs => head fs b) :=
  Bytecode.product recordEncoding encodingNatBool (atom b) (atomEmits b)

noncomputable def multiplierComputes :
    Computes (framedListEncoding recordEncoding) (Expr.encoding encodingNatBool) multiplier :=
  Bytecode.finish (Bytecode.binary _ _ false _ _ (headEmits false) (headEmits true))

noncomputable def computes : Computes (framedListEncoding recordEncoding)
    (pairEncoding (Expr.encoding encodingNatBool) (framedListEncoding recordEncoding))
    (fun fs => (multiplier fs, tail fs)) := pairComputes multiplierComputes tailComputes

theorem atom_size (b : Bool) (r : Record) : (atom b r).size = 1 := by
  simp only [atom]
  split_ifs <;> rfl

theorem multiplier_size (fs : List Record) : (multiplier fs).size ≤ 4 * fs.length + 3 := by
  have h (b : Bool) : (head fs b).size ≤ 2 * fs.length + 1 := by
    apply (Expr.size_product_le _ ?_).trans (by simp)
    intro e he
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
    exact le_of_eq (atom_size b r)
  have hf := h false
  have ht := h true
  simp only [multiplier, Expr.size]
  omega

theorem tail_length (fs : List Record) : (tail fs).length ≤ fs.length := by
  simpa only [tail, List.length_map] using List.length_filter_le keep fs

/-- Natural labels are the byte-level view of the fixed finite coefficient table. -/
def record {n : ℕ} : LabelledFactor ℕ n → Record
  | .scalar c => (0, c, 0, 0, 0)
  | .unary j c => (1, j.val, c false, c true, 0)
  | .link i j p => (2, i.val, j.val, p.toNat, 0)

theorem atom_record {n : ℕ} (f : LabelledFactor ℕ (n + 1)) (b : Bool) :
    atom b (record f) = (Symbolic.splitHead f).1 b := by
  cases f with
  | scalar c => rfl
  | unary j c =>
    refine Fin.cases ?_ (fun j => ?_) j
    · cases b <;> rfl
    · simp [atom, record, Symbolic.splitHead, Fin.succ_ne_zero]
  | link i j p =>
    refine Fin.cases ?_ (fun i => ?_) i
    all_goals refine Fin.cases ?_ (fun j => ?_) j
    all_goals cases b <;> cases p <;>
      simp [atom, record, Symbolic.splitHead, Fin.succ_ne_zero]

theorem tail_record {n : ℕ} (f : LabelledFactor ℕ (n + 1)) :
    (if keep (record f) then some (Rewrite.record (0, false) (record f)) else none) =
      (Symbolic.splitHead f).2.map record := by
  cases f with
  | scalar c => rfl
  | unary j c =>
    refine Fin.cases ?_ (fun j => ?_) j
    all_goals simp [keep, record, Rewrite.record, Rewrite.address, Rewrite.flipAt,
      Symbolic.splitHead, Fin.succ_ne_zero]
  | link i j p =>
    refine Fin.cases ?_ (fun i => ?_) i
    all_goals refine Fin.cases ?_ (fun j => ?_) j
    all_goals cases p <;> simp [keep, record, Rewrite.record, Rewrite.address,
      Rewrite.flipAt, Symbolic.splitHead, Fin.succ_ne_zero]

theorem head_records {n : ℕ} (fs : List (LabelledFactor ℕ (n + 1))) (b : Bool) :
    head (fs.map record) b = Symbolic.head fs b := by
  simp [head, Symbolic.head, List.map_map, Function.comp_def, atom_record]

theorem tail_records {n : ℕ} (fs : List (LabelledFactor ℕ (n + 1))) :
    tail (fs.map record) = (Symbolic.tail fs).map record := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have h := tail_record f
    cases hk : keep (record f) <;> cases hs : (Symbolic.splitHead f).2 <;>
      simp_all [tail, Symbolic.tail]

theorem primitive_bound (fs : List Record) :
    primitiveCost computes.machine (computes.outputs fs).steps
      (some (Turing.initList computes.machine.computer ((framedListEncoding recordEncoding).encode fs))) ≤
      (primitivePolynomial computes).eval ((framedListEncoding recordEncoding).encode fs).length :=
  computes_primitive_cost computes fs

end Holant.LocalDrafts.Tractability.ProductMachine.Isolated
