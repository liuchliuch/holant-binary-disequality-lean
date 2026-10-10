import Holant.Complexity.UniversalPairReduction.Surgery.ChoiceSemantics
import Holant.Complexity.UniversalPairReduction.Surgery.PromisedValidation
import Holant.Complexity.UniversalPairReduction.RawHole

/-! Literal adjoining of one ordered binary table. Old labels and every old
coefficient are preserved; all binary variants share the original source codec. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction.BinaryFamily
open Surgery
open Surgery.Choice
variable {K : Type*} [CommSemiring K] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val))

def signatures (B : BinaryTable K) (i : Fin (s+1)) : Signature K (extendedArity s arity i.val) :=
  fun x => if hi : i.val<s then
    G ⟨i.val,hi⟩ (fun j => x (Fin.cast (by simp [extendedArity,hi]) j))
  else B (x (Fin.cast (by simp [extendedArity,hi]) (0 : Fin 2)))
    (x (Fin.cast (by simp [extendedArity,hi]) (1 : Fin 2)))

 theorem table_old (B : BinaryTable K) (i : ℕ) (hi : i<s) (bits : List Bool) :
    Choice.table (signatures G B) i bits = Choice.table G i bits := by
  have hnew : i<s+1 := by omega
  simp [Choice.table,signatures,hi,hnew]

 theorem table_new (B : BinaryTable K) (bits : List Bool) :
    Choice.table (signatures G B) s bits = B (bits.getD 0 false) (bits.getD 1 false) := by
  simp [Choice.table,signatures]

 theorem table_pair (B : BinaryTable K) (a b : Bool) :
    Choice.table (signatures G B) s [a,b]=B a b := by
  simp [table_new]

 def network (B : BinaryTable K) (r : Input s arity) : Network K 0 :=
  r.val.realize r.property.1 (signatures G B) (fun _ : Fin 1 => Signature.disequality)

 def value (B : BinaryTable K) (r : Input s arity) : K := (network G B r).denote Fin.elim0

 theorem value_evaluate (B : BinaryTable K) (r : Input s arity) :
    value G B r=Choice.evaluate (Choice.table (signatures G B)) r.val.edges.length r.val.vertices :=
  Choice.denote_eq_evaluate r.val r.property.1 (signatures G B)

 theorem vertex_new (B : BinaryTable K) (r : Input s arity) (v : Fin r.val.vertices.length)
    (hv : (r.val.vertices.get v).1=s) (a b : Bool) :
    (network G B r).vertex v
      (fun i => (![a,b] : Fin 2 → Bool) (Fin.cast (by simp [network,RawClosedNetwork.realize,
        RawClosedNetwork.shape,extendedArity,show r.val.vertices[v.val].1=s from hv]) i))=B a b := by
  have hv' : r.val.vertices[v.val].1=s := hv
  simp [network,RawClosedNetwork.realize,RawClosedNetwork.signatureLabel,signatures,hv']

 theorem other_label (r : Input s arity) (v : Fin r.val.vertices.length)
    (hv : (r.val.vertices.get v).1=s) (u : Fin r.val.vertices.length) (hne : u≠v) :
    (r.val.vertices.get u).1<s := by
  have hm : r.val.vertices.get u∈r.val.vertices.eraseIdx v.val :=
    List.mem_eraseIdx_iff_getElem.mpr ⟨u.val,u.isLt,fun h => hne (Fin.ext h),rfl⟩
  exact (Surgery.erased_valid r v hv _ hm).1

 theorem vertex_old_eq (B C : BinaryTable K) (r : Input s arity)
    (v : Fin r.val.vertices.length) (hv : (r.val.vertices.get v).1=s)
    (u : Fin r.val.vertices.length) (hne : u≠v) :
    (network G B r).vertex u=(network G C r).vertex u := by
  have hu := other_label r v hv u hne
  have hu' : r.val.vertices[u.val].1<s := hu
  funext x
  simp [network,RawClosedNetwork.realize,RawClosedNetwork.signatureLabel,signatures,hu']

 theorem weight_old (B : BinaryTable K) (c : ℕ → Bool) (rows : List RawVertex)
    (hr : ∀row∈rows,row.1<s) :
    Choice.weight (Choice.table (signatures G B)) c rows=Choice.weight (Choice.table G) c rows := by
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro row hrow
  exact table_old G B row.1 (hr row hrow) _

 theorem evaluate_old (B : BinaryTable K) (m : ℕ) (rows : List RawVertex)
    (hr : ∀row∈rows,row.1<s) :
    Choice.evaluate (Choice.table (signatures G B)) m rows=Choice.evaluate (Choice.table G) m rows := by
  unfold Choice.evaluate
  apply Finset.sum_congr rfl
  intro c _
  exact weight_old G B _ rows hr

end Holant.Complexity.UniversalPairReduction.BinaryFamily
