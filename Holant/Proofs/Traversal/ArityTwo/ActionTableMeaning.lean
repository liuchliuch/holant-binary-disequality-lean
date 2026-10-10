import Holant.Proofs.Traversal.ArityTwo.ActionTableCompiler
import Holant.Proofs.Traversal.ArityTwo.DescriptorTotal


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.ActionTableMeaning
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution.Compiler PortWalk Descriptors
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s b : ℕ} {arity : ℕ → ℕ} {A : Type}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)

def query (p : r.Ports arity) : RawPortQuery.Input s b arity := ⟨⟨r,h⟩,r.route h p⟩
def address (p : r.Ports arity) := EndpointAddress.value s b arity (query r h p)

@[simp] theorem query_port (p : r.Ports arity) : RawPortQuery.port s b arity (query r h p) = p := by
  apply (r.route_bijective h).1
  exact r.route_lookup h _

theorem address_lt (p : r.Ports arity) : address r h p < 2*r.edges.length :=
  EndpointAddress.value_lt s b arity (query r h p)

theorem address_injective : Function.Injective (address r h) := by
  intro p q hpq
  apply (r.route_bijective h).1
  exact (Holant.LocalDrafts.Tractability.ProductMachine.Endpoint.equivalence r.edges.length).injective
    (Fin.ext hpq)

def vertex := fun v => labels (r.signatureLabel h v)
def edge := fun e => edges (r.edgeLabel h e)

def rows (ctx : ActionTableCompiler.Context) :=
  ActionTableCompiler.table ctx (PortTableCompiler.value s b arity labels edges codec ⟨r,h⟩)

theorem rows_length (ctx : ActionTableCompiler.Context) :
    (rows r h labels edges codec ctx).length = 2*r.edges.length := by
  simp [rows,ActionTableCompiler.table,PortTableCompiler.length]

def body (ctx : ActionTableCompiler.Context) (p : r.Ports arity) :=
  ActionTableCompiler.row ctx (PortInstruction.record s b arity labels edges codec (query r h p))

theorem get_row (ctx : ActionTableCompiler.Context) (p : r.Ports arity) :
    (rows r h labels edges codec ctx).get
      ⟨address r h p,by rw [rows_length]; exact address_lt r h p⟩ =
      body r h labels edges codec ctx p := by
  have hl := PortTableCompiler.get_endpoint s b arity labels edges codec ⟨r,h⟩
    (r.route h p).1 (r.route h p).2
  simpa [rows,ActionTableCompiler.table,List.get_eq_getElem,body,address,query,
    EndpointAddress.value] using congrArg (ActionTableCompiler.row ctx) hl

theorem reference (ctx : ActionTableCompiler.Context) (p : r.Ports arity)
    (out : List Bool) (n : ℕ)
    (hh : Traversal.Expands (rows r h labels edges codec ctx)
      (body r h labels edges codec ctx p) out n) :
    Traversal.Expands (rows r h labels edges codec ctx) (Traversal.reference (address r h p)) out (n+1) := by
  let rs := rows r h labels edges codec ctx
  let i := address r h p
  have hi : i < rs.length := by rw [rows_length]; exact address_lt r h p
  have hr : rs[i] = body r h labels edges codec ctx p := get_row r h labels edges codec ctx p
  have hs : rs = rs.take i ++ body r h labels edges codec ctx p :: rs.drop (i+1) := by
    have hs := List.take_append_drop i rs
    rw [List.drop_eq_getElem_cons hi,hr] at hs
    exact hs.symm
  have hl : (rs.take i).length = i := by simp [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)]
  have he := Traversal.Expands.reference (pending := []) (rs.take i) (rs.drop (i+1))
    (body r h labels edges codec ctx p) hs (by simpa using hh)
  simpa only [List.append_nil,hl] using he

theorem body_terminal (ctx : ActionTableCompiler.Context) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    body r h labels edges codec ctx p = Traversal.literals
      (MatrixEmission.word codec [.literal (unaryTable r (vertex r h labels) p.1 true),
        .literal (unaryTable r (vertex r h labels) p.1 false)]) := by
  have hdeg : degree (arity := arity) (query r h p).1.val p.1 = 1 := hp
  simp only [body, PortInstruction.record, query_port, hdeg, decide_true,
    ite_true, ActionTableCompiler.row]
  change Traversal.literals (MatrixEmission.unaryWord s b arity labels codec
    ⟨⟨r,h⟩, (RawPortQuery.port s b arity (query r h p)).1⟩) = _
  rw [query_port]
  rfl

theorem next_address (p q : r.Ports arity) (ho : other r p = some q) :
    EndpointAddress.value s b arity (PortInstruction.nextQuery s b arity (query r h p)) =
      address r h (cross r h q) := by
  simp [PortInstruction.nextQuery,PortInstruction.exitQuery,PortInstruction.exitPort,
    query_port,ho,address,query,RawPortQuery.port,EndpointAddress.value,route_cross]

theorem body_binary (ctx : ActionTableCompiler.Context) (p q : r.Ports arity)
    (ho : other r p = some q) :
    body r h labels edges codec ctx p =
      ActionTableCompiler.call ctx (address r h (cross r h q)) ++ Traversal.literals
        (MatrixEmission.word codec (matrixStep (edgeTable r h (edge r h edges) q) ++
          matrixStep (binaryTable r (vertex r h labels) p))) := by
  have hd := (other_some r p q ho).2.2
  have hbin := PortInstruction.binary_exact s b arity labels edges codec (query r h p) q
    (by simpa [query, RawPortQuery.port] using ho)
  have hdeg : degree (arity := arity) (query r h p).1.val p.1 = 2 := hd
  simp only [body, PortInstruction.record, query_port, hdeg, Nat.reduceEqDiff,
    decide_false, ite_false, ActionTableCompiler.row]
  rw [next_address r h p q ho, hbin]
  simp only [query_port]
  rfl

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.ActionTableMeaning
