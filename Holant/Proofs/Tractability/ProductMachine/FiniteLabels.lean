import Holant.Proofs.Tractability.ProductMachine.Semantics
import Holant.Proofs.Tractability.ProductMachine.FieldInterpreter


namespace Holant.LocalDrafts.Tractability.ProductMachine.FiniteLabels

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler Holant.Algebraic
open ProductElimination (LabelledFactor)
open Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.GraphLabelEncoding

def mapExpr {A B : Type} (f : A → B) : Expr A → Expr B
  | .zero => .zero
  | .one => .one
  | .literal a => .literal (f a)
  | .add a b => .add (mapExpr f a) (mapExpr f b)
  | .mul a b => .mul (mapExpr f a) (mapExpr f b)

def mapFactor {A B : Type} {n : ℕ} (f : A → B) : LabelledFactor A n → LabelledFactor B n
  | .scalar a => .scalar (f a)
  | .unary j a => .unary j (fun b => f (a b))
  | .link i j p => .link i j p

theorem map_product {A B : Type} (f : A → B) (es : List (Expr A)) :
    mapExpr f (Expr.product es) = Expr.product (es.map (mapExpr f)) := by
  induction es <;> simp_all [Expr.product, mapExpr]

theorem map_atom {A B : Type} (f : A → B) {n : ℕ} (a : LabelledFactor A n) (x : Fin n → Bool) :
    Symbolic.atom (mapFactor f a) x = mapExpr f (Symbolic.atom a x) := by
  cases a <;> simp [mapFactor, Symbolic.atom, mapExpr]
  split <;> rfl

theorem map_substitute {A B : Type} (f : A → B) {m n : ℕ} (r : Fin m → Fin n × Bool)
    (a : LabelledFactor A m) :
    Symbolic.substitute r (mapFactor f a) = mapFactor f (Symbolic.substitute r a) := by cases a <;> rfl

theorem map_pivot {A B : Type} (f : A → B) {n : ℕ} (fs : List (LabelledFactor A (n + 1))) :
    Symbolic.pivot (fs.map (mapFactor f)) = Symbolic.pivot fs := by
  have one (a : LabelledFactor A (n + 1)) :
      (mapFactor f a).realize (fun _ => (0 : ℕ)) = a.realize (fun _ => (0 : ℕ)) := by cases a <;> rfl
  simp [Symbolic.pivot, List.map_map, Function.comp_def, one]

theorem map_split {A B : Type} (f : A → B) {n : ℕ} (a : LabelledFactor A (n + 1)) :
    Symbolic.splitHead (mapFactor f a) =
      ((fun b => mapExpr f ((Symbolic.splitHead a).1 b)),
        (Symbolic.splitHead a).2.map (mapFactor f)) := by
  cases a with
  | scalar a => rfl
  | unary j a => refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  | link i j p =>
    refine Fin.cases ?_ (fun i => ?_) i
    all_goals refine Fin.cases ?_ (fun j => ?_) j
    all_goals cases p <;> simp [Symbolic.splitHead, mapFactor, mapExpr]

theorem map_head {A B : Type} (f : A → B) {n : ℕ} (fs : List (LabelledFactor A (n + 1))) (b : Bool) :
    Symbolic.head (fs.map (mapFactor f)) b = mapExpr f (Symbolic.head fs b) := by
  simp [Symbolic.head, map_product, List.map_map, Function.comp_def, map_split]

theorem map_tail {A B : Type} (f : A → B) {n : ℕ} (fs : List (LabelledFactor A (n + 1))) :
    Symbolic.tail (fs.map (mapFactor f)) = (Symbolic.tail fs).map (mapFactor f) := by
  induction fs with
  | nil => rfl
  | cons a fs ih =>
    simp only [Symbolic.tail, List.map_cons, List.filterMap_cons, map_split] at *
    cases (Symbolic.splitHead a).2 <;> simp_all

theorem map_compileAcc {A B : Type} (f : A → B) {n : ℕ} (fs : List (LabelledFactor A n)) (acc : Expr A) :
    Semantics.compileAcc (fs.map (mapFactor f)) (mapExpr f acc) =
      mapExpr f (Semantics.compileAcc fs acc) := by
  induction n generalizing acc with
  | zero => simp [Semantics.compileAcc, mapExpr, map_product, List.map_map, Function.comp_def, map_atom]
  | succ n ih =>
    cases hp : Symbolic.pivot fs with
    | none =>
      simpa only [Semantics.compileAcc, map_pivot, hp, map_tail, map_head, mapExpr] using
        ih (Symbolic.tail fs) (.mul acc (.add (Symbolic.head fs false) (Symbolic.head fs true)))
    | some jp =>
      rcases jp with ⟨j, p⟩
      simpa only [Semantics.compileAcc, map_pivot, hp, List.map_map, Function.comp_def, map_substitute] using
        ih (fs.map (Symbolic.substitute (ProductElimination.redirect j p))) acc

variable (q n : ℕ)

def decodeRecord (r : Templates.Record) : Option (LabelledFactor (Fin q) n) :=
  if r.1 = 0 then
    if hc : r.2.1 < q then some (.scalar ⟨r.2.1, hc⟩) else none
  else if r.1 = 1 then
    if hi : r.2.1 < n then
      if hc : r.2.2.1 < q then
        if hd : r.2.2.2.1 < q then
          some (.unary ⟨r.2.1, hi⟩ (fun b => if b then ⟨r.2.2.2.1, hd⟩ else ⟨r.2.2.1, hc⟩))
        else none
      else none
    else none
  else if r.1 = 2 then
    if hi : r.2.1 < n then
      if hj : r.2.2.1 < n then some (.link ⟨r.2.1, hi⟩ ⟨r.2.2.1, hj⟩ (r.2.2.2.1 != 0)) else none
    else none
  else none

theorem decode_record (f : LabelledFactor (Fin q) n) :
    decodeRecord q n (Isolated.record (mapFactor Fin.val f)) = some f := by
  cases f with
  | scalar a => simp [decodeRecord, Isolated.record, mapFactor, a.isLt]
  | unary j a =>
    have hfun : (fun b => if b then a true else a false) = a := by funext b; cases b <;> rfl
    simpa [decodeRecord, Isolated.record, mapFactor, j.isLt, (a false).isLt, (a true).isLt] using
      congrArg (fun u => some (LabelledFactor.unary j u)) hfun
  | link i j p => cases p <;> simp [decodeRecord, Isolated.record, mapFactor, i.isLt, j.isLt]

def factorEncoding : Encoding (LabelledFactor (Fin q) n) Bool where
  encode f := Templates.recordEncoding.encode (Isolated.record (mapFactor Fin.val f))
  decode bits := (Templates.recordEncoding.decode bits).bind (decodeRecord q n)
  decode_encode f := by simp [decode_record]

abbrev Input := Σ n : ℕ, List (LabelledFactor (Fin q) n)
def inputEncoding : Encoding (Input q) Bool :=
  sigmaEncoding UnaryBinary.unaryEncoding (fun n => framedListEncoding (factorEncoding q n))

theorem table_encode (fs : List (LabelledFactor (Fin q) n)) :
    ((framedListEncoding Templates.recordEncoding).encode
      ((fs.map (mapFactor Fin.val)).map Isolated.record)) =
        ((framedListEncoding (factorEncoding q n)).encode fs) := by
  induction fs <;> simp_all [framedListEncoding, framedListEncode, factorEncoding]

noncomputable def «initialize» : Computes (inputEncoding q) Round.encoding
    (fun x => Semantics.state (x.2.map (mapFactor Fin.val)) .one) := by
  let raw : Computes (inputEncoding q)
      (pairEncoding UnaryBinary.unaryEncoding (framedListEncoding Templates.recordEncoding))
      (fun x => (x.1, (x.2.map (mapFactor Fin.val)).map Isolated.record)) :=
    recode (identityComputes (pairEncoding UnaryBinary.unaryEncoding
      (framedListEncoding Templates.recordEncoding)))
      (fun x => (x.1, (x.2.map (mapFactor Fin.val)).map Isolated.record))
      (fun x => by
        change Holant.Algebraic.frame _ ++ _ = Holant.Algebraic.frame _ ++ _
        rw [table_encode]) (fun _ => rfl)
  exact pairComputes (raw.andThen (Wiring.firstComputes _ _))
    (pairComputes (raw.andThen (Wiring.secondComputes _ _))
      (constantComputes (inputEncoding q) (Expr.encoding encodingNatBool) .one))

theorem expression_encode (e : Expr (Fin q)) :
    ((Expr.encoding encodingNatBool).encode (mapExpr Fin.val e)) =
      ((Expr.encoding (SignatureLabel.binaryFinEncoding q)).encode e) := by
  have code (e : Expr (Fin q)) : (mapExpr Fin.val e).code = e.code.map (fun op =>
      match op with
      | .literal a => .literal a.val
      | .zero => .zero | .one => .one | .add => .add | .mul => .mul
      | .swap => .swap | .copy i => .copy i | .erase i => .erase i) := by
    induction e <;> simp_all [mapExpr, Expr.code]
  change ((codeEncoding encodingNatBool).encode (mapExpr Fin.val e).code) =
    ((codeEncoding (SignatureLabel.binaryFinEncoding q)).encode e.code)
  rw [code]
  generalize e.code = ops
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;>
      simp_all [Expr.encoding, codeEncoding, framedListEncoding, framedListEncode,
        opEncoding, opEncode, encodingNatBool, SignatureLabel.binaryFinEncoding]

def expression (x : Input q) := Semantics.compileAcc x.2 .one

/-- Same concrete compiler, with finite labels justified by byte equality. -/
noncomputable def compiler :
    Computes (inputEncoding q) (Expr.encoding (SignatureLabel.binaryFinEncoding q)) (expression q) :=
  recode ((«initialize» q).andThen Compilation.stateComputes) id (fun _ => rfl) (fun x => by
    dsimp only [Function.comp_apply, id_eq]
    rw [Semantics.stateExpression_eq]
    change ((Expr.encoding encodingNatBool).encode
      (Semantics.compileAcc (x.2.map (mapFactor Fin.val)) (mapExpr (Fin.val : Fin q → ℕ) .one))) = _
    rw [map_compileAcc, expression_encode]
    rfl)

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (table : Fin q → Fin d → ℚ)

noncomputable def answer (x : Input q) := ProductElimination.partition
  (x.2.map (LabelledFactor.realize (FieldInterpreter.coefficients F table)))

/-- Actual encoded factor-input solver, including all arbitrary-precision field
operations. This does not yet claim a raw signature-family Holant solver. -/
noncomputable def computes : Computes (inputEncoding q) F.encoding (answer q F table) :=
  congrComputes ((compiler q).andThen
    (FieldInterpreter.computes F table (SignatureLabel.binaryFinEncoding q) q.size
      (SignatureLabel.binaryFinEncoding_length_le q))) (fun x => by
        simp [expression, answer, Semantics.compileAcc_eval, Expr.eval,
          ProductElimination.evaluate_eq_partition])

theorem primitive_bound (x : Input q) :
    let w := computes q F table
    primitiveCost w.machine (w.outputs x).steps
      (some (Turing.initList w.machine.computer ((inputEncoding q).encode x))) ≤
      (primitivePolynomial w).eval ((inputEncoding q).encode x).length :=
  computes_primitive_cost (computes q F table) x

end Holant.LocalDrafts.Tractability.ProductMachine.FiniteLabels
