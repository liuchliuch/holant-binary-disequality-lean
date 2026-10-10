import Holant.Complexity.UniversalPairReduction.Surgery.Endpoints
import Holant.NativeNetwork

/-! Literal raw-record native-X evaluation by one Boolean choice per edge.
This is proved equal to the original decoded Network.denote; it is used only
for semantic surgery and is not charged as a polynomial-time evaluator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction.Surgery.Choice
open RawClosedNetwork
open scoped BigOperators
variable {K : Type*} [CommSemiring K]

abbrev Table (K : Type*) := ℕ → List Bool → K

def extend {m : ℕ} (c : Fin m → Bool) (i : ℕ) : Bool := if hi : i<m then c ⟨i,hi⟩ else false

def bit (c : ℕ → Bool) (p : RawEndpoint) : Bool := if p.2 then c p.1 else !(c p.1)

def rowValue (F : Table K) (c : ℕ → Bool) (row : RawVertex) : K :=
  F row.1 (row.2.map (bit c))

def weight (F : Table K) (c : ℕ → Bool) (rows : List RawVertex) : K :=
  (rows.map (rowValue F c)).prod

def evaluate (F : Table K) (m : ℕ) (rows : List RawVertex) : K :=
  ∑c : Fin m → Bool,weight F (extend c) rows

/-- A total table extending the exact fixed signatures only on malformed rows. -/
def table {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (arity i.val)) : Table K := fun label bits =>
  if hi : label<s then G ⟨label,hi⟩ (fun i => bits.getD i.val false) else 0

 theorem assigned_port {s : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)
    (hr : r.WellFormed s 1 arity) (c : Fin r.edges.length → Bool)
    (v : Fin r.vertices.length) (i : Fin (arity (r.vertices.get v).1)) :
    (r.shape hr).assignment Fin.elim0 (Network.endpointChoiceAssignment c) v i =
      ((r.vertices.get v).2.map (bit (extend c))).getD i.val false := by
  have hi : i.val<(r.vertices.get v).2.length := by rw [(hr.1 v).2]; exact i.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map]
  change Network.endpointChoiceAssignment c (r.route hr ⟨v,i⟩)=_
  have he := r.portEndpoint_bound hr ⟨v,i⟩
  simp only [Network.endpointChoiceAssignment,route,bit,extend]
  simp only [portEndpoint,List.get_eq_getElem,Fin.val_cast] at he ⊢
  simp only [dif_pos he]

/-- The original faithful decoder has exactly this native-X assignment sum. -/
theorem denote_eq_evaluate {s : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)
    (hr : r.WellFormed s 1 arity) (G : (i : Fin s) → Signature K (arity i.val)) :
    (r.realize hr G (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 =
      evaluate (table G) r.edges.length r.vertices := by
  change (Network.mk (r.shape hr) _ (fun _ => Signature.disequality)).denote Fin.elim0=_
  rw [Network.denote_disequality]
  unfold Network.endpointChoiceDenote evaluate weight
  apply Finset.sum_congr rfl
  intro c _
  rw [←List.prod_ofFn]
  have he : List.ofFn (fun v : Fin r.vertices.length =>
      G (r.signatureLabel hr v)
        ((r.shape hr).assignment Fin.elim0 (Network.endpointChoiceAssignment c) v)) =
      r.vertices.map (rowValue (table G) (extend c)) := by
    rw [←List.ofFn_getElem_eq_map r.vertices]
    apply congrArg List.ofFn
    funext v
    change G (r.signatureLabel hr v) _ = rowValue (table G) (extend c) (r.vertices.get v)
    unfold rowValue table
    rw [dif_pos (hr.1 v).1]
    congr 1
    funext i
    exact assigned_port r hr c v i
  exact congrArg List.prod he

 theorem weight_perm (F : Table K) (c : ℕ → Bool) {a b : List RawVertex}
    (h : a.Perm b) : weight F c a=weight F c b := (h.map _).prod_eq

 theorem weight_cons (F : Table K) (c : ℕ → Bool) (row : RawVertex) (rows : List RawVertex) :
    weight F c (row::rows)=rowValue F c row*weight F c rows := rfl

end Holant.Complexity.UniversalPairReduction.Surgery.Choice
