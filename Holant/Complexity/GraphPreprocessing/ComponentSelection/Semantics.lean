import Holant.OneHot.Computable.Tables

/-! Endpoint-local parent tests characterize global unused original edges.
The surplus scan retains literal original edge order, including loops and
parallel edges, without an all-vertex search for each edge. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def edgeUsed (g : Graph) (e : g.Edge) : Bool :=
  decide ((g.parentRow (g.endpoint e false)).parent.map Prod.fst=some e.val) ||
    decide ((g.parentRow (g.endpoint e true)).parent.map Prod.fst=some e.val)
def Unused (g : Graph) (e : g.Edge) : Prop :=
  ∀ v : g.Vertex, ∀ q∈(g.parentRow v).parent, q.1≠e.val
instance (g : Graph) (e : g.Edge) : Decidable (Unused g e) := inferInstanceAs (Decidable (∀ v, ∀ q∈_, _))

theorem edgeUsed_iff (g : Graph) (e : g.Edge) :
    edgeUsed g e=true ↔ ∃ v : g.Vertex, ∃ q, (g.parentRow v).parent=some q ∧ q.1=e.val := by
  have local_iff (side : Bool) :
      (g.parentRow (g.endpoint e side)).parent.map Prod.fst=some e.val ↔
        ∃ q, (g.parentRow (g.endpoint e side)).parent=some q ∧ q.1=e.val := by
    cases hp : (g.parentRow (g.endpoint e side)).parent <;> simp [hp]
  simp only [edgeUsed,Bool.or_eq_true,decide_eq_true_eq,local_iff]
  constructor
  · rintro (⟨q,hq,he⟩|⟨q,hq,he⟩)
    · exact ⟨g.endpoint e false,q,hq,he⟩
    · exact ⟨g.endpoint e true,q,hq,he⟩
  · rintro ⟨v,q,hq,he⟩
    obtain ⟨e',he',hend,_⟩ := g.parentRow_some_spec v q hq
    have ee : e'=e := Fin.ext (he'.trans he)
    subst e'
    rw [←hend] at hq
    cases hz : q.2
    · exact Or.inl ⟨q,by simpa [hz] using hq,he⟩
    · exact Or.inr ⟨q,by simpa [hz] using hq,he⟩

theorem unused_iff (g : Graph) (e : g.Edge) : edgeUsed g e=false ↔ Unused g e := by
  have h := edgeUsed_iff g e
  unfold Unused
  simp only [Option.mem_def]
  cases hu : edgeUsed g e <;> simp only [hu,Bool.false_eq_true,Bool.true_eq_false,true_iff,false_iff] at h ⊢
  · intro v q hq he
    exact h ⟨v,q,hq,he⟩
  · intro hall
    obtain ⟨v,q,hq,he⟩ := h
    exact hall v q hq he

def surplusEdges (g : Graph) (root : g.Vertex) : List g.Edge :=
  (List.finRange g.edges.length).filter fun e =>
    decide (g.label (g.endpoint e false)=root) && !edgeUsed g e
theorem mem_surplusEdges (g : Graph) (root : g.Vertex) (e : g.Edge) :
    e∈surplusEdges g root ↔ g.label (g.endpoint e false)=root ∧ Unused g e := by
  simp [surplusEdges,unused_iff]
theorem surplus_unused (g : Graph) (root : g.Vertex) (e : g.Edge) (h : e∈surplusEdges g root) :
    Unused g e := ((mem_surplusEdges g root e).mp h).2
theorem surplus_nodup (g : Graph) (root : g.Vertex) : (surplusEdges g root).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange _)
theorem surplus_sublist (g : Graph) (root : g.Vertex) :
    (surplusEdges g root).Sublist (List.finRange g.edges.length) := List.filter_sublist
theorem surplus_length_le (g : Graph) (root : g.Vertex) : (surplusEdges g root).length≤g.edges.length := by
  simpa using (surplus_sublist g root).length_le

inductive Classification where
  | tree
  | unicycle (edge : ℕ)
  | dense
  deriving DecidableEq, Repr
def classify (edges : List ℕ) : Classification := match edges with
  | [] => .tree
  | [e] => .unicycle e
  | _::_::_ => .dense
def classification (g : Graph) (root : g.Vertex) : Classification := classify ((surplusEdges g root).map Fin.val)
theorem classify_tree (es : List ℕ) : classify es=.tree ↔ es=[] := by
  cases es with
  | nil => simp [classify]
  | cons e es => cases es <;> simp [classify]
theorem classify_unicycle (es : List ℕ) (e : ℕ) : classify es=.unicycle e ↔ es=[e] := by
  cases es with
  | nil => simp [classify]
  | cons f es => cases es <;> simp [classify]
theorem classify_dense (es : List ℕ) : classify es=.dense ↔ 2≤es.length := by
  cases es with
  | nil => simp [classify]
  | cons e es => cases es <;> simp [classify]
theorem unicycle_unused (g : Graph) (root : g.Vertex) (e : ℕ)
    (h : classification g root=.unicycle e) :
    ∃ q : g.Edge, q.val=e ∧ Unused g q ∧ g.label (g.endpoint q false)=root := by
  have hs := (classify_unicycle _ e).mp h
  have hm : e∈(surplusEdges g root).map Fin.val := by rw [hs]; simp
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
  obtain ⟨hc,hu⟩ := (mem_surplusEdges g root q).mp hq
  exact ⟨q,he,hu,hc⟩
end Holant.Complexity.GraphPreprocessing.ComponentSelection
