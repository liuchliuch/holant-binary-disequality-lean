import Holant.Proofs.Tractability.ProductMachine.FiniteLabels
import Holant.Proofs.Tractability.ProductNetwork
import Holant.Complexity.ClosedNetworkSemantics


namespace Holant.LocalDrafts.Tractability.ProductMachine.RawFamily

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler Holant.Algebraic
open ProductElimination (LabelledFactor)
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {q n m : ℕ}

def template : LabelledFactor (Fin q) n → Templates.LocalFactor
  | .scalar a => .scalar a.val
  | .unary j a => .unary j.val (a false).val (a true).val
  | .link i j p => .link i.val j.val p

def rename (r : Fin n → Fin m) (f : LabelledFactor (Fin q) n) : LabelledFactor (Fin q) m :=
  Symbolic.substitute (fun i => (r i, false)) f

theorem place_template (E : ℕ) (ports : List RawEndpoint) (route : Fin n → Fin E × Bool)
    (hp : ∀ i, ports.getD i.val (0, false) = ((route i).1.val, (route i).2))
    (f : LabelledFactor (Fin q) n) :
    Templates.place ports (template f) =
      Isolated.record (FiniteLabels.mapFactor Fin.val (rename (fun i => Endpoint.typed E (route i)) f)) := by
  have hp' (i : Fin n) : (ports[i.val]?).getD (0,false) = ((route i).1.val,(route i).2) := hp i
  cases f <;> simp [hp', template, Templates.place, hp, rename, Symbolic.substitute,
    FiniteLabels.mapFactor, Isolated.record, Endpoint.typed]

variable (q s b : ℕ) (arity : ℕ → ℕ)
variable (vertices : (i : Fin s) → List (LabelledFactor (Fin q) (arity i.val)))
variable (edges : Fin b → List (LabelledFactor (Fin q) 2))

def vertexTemplates (i : Fin s) := (vertices i).map template
def edgeTemplates (i : Fin b) := (edges i).map template

def vertexFactors (r : Input s b arity) (v : Fin r.val.vertices.length) :
    List (LabelledFactor (Fin q) (2 * r.val.edges.length)) :=
  (vertices (r.val.signatureLabel r.property v)).map
    (rename (fun i => Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v, i⟩)))

def edgeFactors (r : Input s b arity) (e : Fin r.val.edges.length) :
    List (LabelledFactor (Fin q) (2 * r.val.edges.length)) :=
  (edges (r.val.edgeLabel r.property e)).map
    (rename (fun i : Fin 2 => Endpoint.typed r.val.edges.length (e, i == 1)))

def factors (r : Input s b arity) : List (LabelledFactor (Fin q) (2 * r.val.edges.length)) :=
  (List.finRange r.val.vertices.length).flatMap (vertexFactors q s b arity vertices r) ++
    (List.finRange r.val.edges.length).flatMap (edgeFactors q s b arity edges r)

theorem vertex_ports (r : Input s b arity) (v : Fin r.val.vertices.length)
    (i : Fin (arity (r.val.vertices.get v).1)) :
    (r.val.vertices.get v).2.getD i.val (0, false) = r.val.portEndpoint r.property ⟨v, i⟩ := by
  have hi : i.val < (r.val.vertices.get v).2.length := by rw [(r.property.1 v).2]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  rfl

theorem vertex_records (r : Input s b arity) (v : Fin r.val.vertices.length) :
    ((vertexTemplates q s arity vertices (sourceLabel s b arity ⟨r, v⟩)).map
      (Templates.place (r.val.vertices.get v).2)) =
    ((vertexFactors q s b arity vertices r v).map (FiniteLabels.mapFactor Fin.val)).map Isolated.record := by
  simp only [vertexTemplates, vertexFactors, List.map_map, Function.comp_def]
  dsimp only [sourceLabel, RawClosedNetwork.signatureLabel]
  try simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro f _
  exact place_template r.val.edges.length _ (fun i => r.val.route r.property ⟨v, i⟩)
    (fun i => vertex_ports s b arity r v i) f

theorem edge_records (r : Input s b arity) (e : Fin r.val.edges.length) :
    ((edgeTemplates q b edges (RawCompiler.edgeLabel s b arity ⟨r, e⟩)).map
      (Templates.place [(e.val, false), (e.val, true)])) =
    ((edgeFactors q s b arity edges r e).map (FiniteLabels.mapFactor Fin.val)).map Isolated.record := by
  simp only [edgeTemplates, edgeFactors, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro f _
  exact place_template r.val.edges.length _ (fun i : Fin 2 => (e, i == 1))
    (fun i => by fin_cases i <;> rfl) f

theorem records_exact (r : Input s b arity) :
    RawCompiler.factors s b arity (vertexTemplates q s arity vertices) (edgeTemplates q b edges) r =
      ((factors q s b arity vertices edges r).map (FiniteLabels.mapFactor Fin.val)).map Isolated.record := by
  simp only [RawCompiler.factors, factors, List.map_append, List.map_flatMap,
    vertex_records, edge_records]

def input (r : Input s b arity) : FiniteLabels.Input q :=
  ⟨2 * r.val.edges.length, factors q s b arity vertices edges r⟩

/-- The raw graph compiler emits the finite solver's input codec literally.
No unbounded natural-to-Fin conversion runs on the host or inside a register. -/
noncomputable def prepare :
    Computes (RawClosedNetwork.validatedEncoding s b arity) (FiniteLabels.inputEncoding q)
      (input q s b arity vertices edges) := by
  let initial := Compilation.initialComputes s b arity
    (vertexTemplates q s arity vertices) (edgeTemplates q b edges)
  let onlyFactors := initial.andThen (pairComputes Round.count Round.factors)
  refine recode onlyFactors id (fun _ => rfl) ?_
  intro r
  dsimp only [Function.comp_apply, id_eq, Compilation.initial]
  change Holant.Algebraic.frame _ ++ _ = _
  rw [records_exact, FiniteLabels.table_encode]
  rfl

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (table : Fin q → Fin d → ℚ)

noncomputable def codeComputes :
    Computes (RawClosedNetwork.validatedEncoding s b arity)
      (Expr.encoding (SignatureLabel.binaryFinEncoding q))
      (fun r => FiniteLabels.expression q (input q s b arity vertices edges r)) :=
  (prepare q s b arity vertices edges).andThen (FiniteLabels.compiler q)

noncomputable def coordinatePolynomial : Polynomial ℕ :=
  (FieldInterpreter.widthPolynomial F table).comp
    (codeComputes q s b arity vertices edges).outputBound.bound

/-- Coordinate bounds in original raw-input bits, using the actual compiler's
output-length theorem, then the structural arithmetic proof. -/
theorem coordinate_trace_bound (r : Input s b arity) :
    let e := FiniteLabels.expression q (input q s b arity vertices edges r)
    ∀ x ∈ e.trace (FieldInterpreter.coefficients F table), ∀ i : Fin d,
      rationalBitHeight (F.decode.symm x i) ≤
        (coordinatePolynomial q s b arity vertices edges F table).eval
          (RawClosedNetwork.encoding.encode r.val).length := by
  let e := FiniteLabels.expression q (input q s b arity vertices edges r)
  have hout := (codeComputes q s b arity vertices edges).outputBound.length_le r
  have hs := (Expr.size_le_encoded (SignatureLabel.binaryFinEncoding q) e).trans hout
  have h := (FieldInterpreter.coordinate_trace_bound F table e _ hs).2
  simpa only [coordinatePolynomial, Polynomial.eval_comp,
    FieldInterpreter.widthPolynomial_eval, e, RawClosedNetwork.validatedEncoding] using h

noncomputable def answer (r : Input s b arity) :=
  ProductElimination.partition ((factors q s b arity vertices edges r).map
    (LabelledFactor.realize (FieldInterpreter.coefficients F table)))

noncomputable def computes :
    Computes (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (answer q s b arity vertices edges F table) :=
  (prepare q s b arity vertices edges).andThen (FiniteLabels.computes q F table)

/-- Every record parser, finite-template dispatch, physical elimination round,
bytecode operation and rational arithmetic primitive belongs to this witness. -/
theorem primitive_bound (r : Input s b arity) :
    let w := computes q s b arity vertices edges F table
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
      (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes q s b arity vertices edges F table) r

variable (signatures : (i : Fin s) → Holant.Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)

/-- Local family formula data, at a fixed finite label, rather than a global
algorithm correctness hypothesis. In particular scalar and nullary factors count. -/
structure LocalFormulas : Prop where
  vertex : ∀ i x, ProductElimination.weight
    ((vertices i).map (LabelledFactor.realize (FieldInterpreter.coefficients F table))) x = signatures i x
  edge : ∀ i x, ProductElimination.weight
    ((edges i).map (LabelledFactor.realize (FieldInterpreter.coefficients F table))) x = kernels i (x 0) (x 1)

variable (laws : LocalFormulas q s b arity vertices edges F table signatures kernels)

theorem weight_rename {k l : ℕ} (r : Fin k → Fin l) (fs : List (LabelledFactor (Fin q) k))
    (x : Fin l → Bool) :
    ProductElimination.weight ((fs.map (rename r)).map
      (LabelledFactor.realize (FieldInterpreter.coefficients F table))) x =
    ProductElimination.weight (fs.map (LabelledFactor.realize (FieldInterpreter.coefficients F table)))
      (fun i => x (r i)) := by
  simp only [rename, List.map_map, Function.comp_def, Symbolic.substitute_realize]
  simpa [Function.comp_def] using ProductElimination.weight_substitute (fun i => (r i, false))
    (fs.map (LabelledFactor.realize (FieldInterpreter.coefficients F table))) x

theorem weight_blocks {k l : ℕ} (fs : Fin k → List (LabelledFactor (Fin q) l)) (x : Fin l → Bool) :
    ProductElimination.weight (((List.finRange k).flatMap fs).map
      (LabelledFactor.realize (FieldInterpreter.coefficients F table))) x =
      ∏ i, ProductElimination.weight ((fs i).map
        (LabelledFactor.realize (FieldInterpreter.coefficients F table))) x := by
  simpa [List.flatMap_def, List.map_flatten, List.map_map, Function.comp_def, List.ofFn_eq_map] using
    ProductElimination.weight_blocks
      (fun i => (fs i).map (LabelledFactor.realize (FieldInterpreter.coefficients F table))) x

def assignmentEquiv (r : Input s b arity) :
    (Fin (2 * r.val.edges.length) → Bool) ≃ ((Fin r.val.edges.length × Bool) → Bool) where
  toFun x e := x (Endpoint.typed r.val.edges.length e)
  invFun x i := x ((Endpoint.equivalence r.val.edges.length).symm i)
  left_inv x := by funext i; exact congrArg x ((Endpoint.equivalence r.val.edges.length).apply_symm_apply i)
  right_inv x := by funext e; exact congrArg x ((Endpoint.equivalence r.val.edges.length).symm_apply_apply e)

include laws in
/-- Derived equality with the original network denotation under the actual raw
endpoint permutation. Loops, parallel edges and empty factors are retained. -/
theorem answer_exact (r : Input s b arity) :
    answer q s b arity vertices edges F table r =
      (r.val.realize r.property signatures kernels).denote Fin.elim0 := by
  have vertex (v : Fin r.val.vertices.length) (x : Fin (2 * r.val.edges.length) → Bool) :
      ProductElimination.weight ((vertexFactors q s b arity vertices r v).map
        (LabelledFactor.realize (FieldInterpreter.coefficients F table))) x =
      signatures (r.val.signatureLabel r.property v)
        (fun i => x (Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v, i⟩))) := by
    unfold vertexFactors
    dsimp only [RawClosedNetwork.signatureLabel]
    rw [weight_rename]
    exact laws.vertex (r.val.signatureLabel r.property v)
      (fun i => x (Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v,i⟩)))
  have edge (e : Fin r.val.edges.length) (x : Fin (2 * r.val.edges.length) → Bool) :
      ProductElimination.weight ((edgeFactors q s b arity edges r e).map
        (LabelledFactor.realize (FieldInterpreter.coefficients F table))) x =
      kernels (r.val.edgeLabel r.property e) (x (Endpoint.typed r.val.edges.length (e, false)))
        (x (Endpoint.typed r.val.edges.length (e, true))) := by
    rw [edgeFactors, weight_rename, laws.edge]
    rfl
  unfold answer ProductElimination.partition Holant.Network.denote
  simp only [factors, List.map_append, ProductElimination.weight_append,
    weight_blocks, vertex, edge]
  change (∑ x : Fin (2 * r.val.edges.length) → Bool, (∏ v, signatures (r.val.signatureLabel r.property v)
    (fun i => x (Endpoint.typed r.val.edges.length (r.val.route r.property ⟨v,i⟩)))) *
    ∏ e, kernels (r.val.edgeLabel r.property e) (x (Endpoint.typed r.val.edges.length (e,false)))
      (x (Endpoint.typed r.val.edges.length (e,true)))) = _
  have hreindex := (assignmentEquiv s b arity r).sum_comp (fun z =>
      (∏ v, signatures (r.val.signatureLabel r.property v) (fun i => z (r.val.route r.property ⟨v,i⟩))) *
        ∏ e, kernels (r.val.edgeLabel r.property e) (z (e,false)) (z (e,true)))
  apply hreindex.trans
  apply Finset.sum_congr rfl
  intro z _
  congr 1

noncomputable def holantComputes :
    Computes (RawClosedNetwork.validatedEncoding s b arity) F.encoding
      (fun r => (r.val.realize r.property signatures kernels).denote Fin.elim0) :=
  congrComputes (computes q s b arity vertices edges F table)
    (answer_exact q s b arity vertices edges F table signatures kernels laws)

end Holant.LocalDrafts.Tractability.ProductMachine.RawFamily
