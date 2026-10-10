import Holant.Marked.WeightedGauge.Basic
import Holant.Network

/-! Gauge transport for the actual finite network assignment sum. The port set
is computed solely from the fixed incidence bijection and endpoint orientations. -/
noncomputable section
namespace Holant.Marked.WeightedGauge
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}

abbrev Port (s : NetworkShape n) := Σ v : Fin s.vertices, Fin (s.arity v)

def selectedEnd (s : NetworkShape n) (orientation : Fin s.edges → Bool) (p : Port s) : Bool :=
  match s.ports p with
  | .inl _ => false
  | .inr (e,b) => b == orientation e

def selectedPorts (s : NetworkShape n) (orientation : Fin s.edges → Bool) : Finset (Port s) :=
  Finset.univ.filter fun p => selectedEnd s orientation p

def selectedAt (s : NetworkShape n) (orientation : Fin s.edges → Bool) (v : Fin s.vertices) :
    Finset (Fin (s.arity v)) := Finset.univ.filter fun i => selectedEnd s orientation ⟨v,i⟩

def portScale (s : NetworkShape n) (orientation : Fin s.edges → Bool) (d : K) (p : Port s) : K :=
  if selectedEnd s orientation p then d else 1

def pushedVertex (s : NetworkShape n) (orientation : Fin s.edges → Bool) (d : K)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) (v : Fin s.vertices) :
    Signature K (s.arity v) := gauge (fun i => portScale s orientation d ⟨v,i⟩) (f v)

def weightedEdge (d : K) (orientation : Bool) (M : Kernel K) : Kernel K :=
  if orientation then Kernel.mul M (diagonal d) else Kernel.mul (diagonal d) M

theorem weightedEdge_apply (d : K) (orientation : Bool) (M : Kernel K) (a b : Bool) :
    weightedEdge d orientation M a b = bitWeight d (if orientation then b else a) * M a b := by
  cases orientation <;> simp [weightedEdge, diagonal_mul, mul_diagonal, mul_comm]

/-- The selected set has exactly the original first/second occurrences specified by the skeleton. -/
theorem selectedPorts_eq_image (s : NetworkShape n) (orientation : Fin s.edges → Bool) :
    selectedPorts s orientation = Finset.univ.image (fun e => s.ports.symm (.inr (e,orientation e))) := by
  classical
  ext p
  simp only [selectedPorts, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, exists_prop]
  constructor
  · intro hp
    cases he : s.ports p with
    | inl i => simp [selectedEnd, he] at hp
    | inr eb =>
      obtain ⟨e,b⟩ := eb
      have hb : b = orientation e := by simpa [selectedEnd, he] using hp
      refine ⟨e, ?_⟩
      rw [← hb, ← he, Equiv.symm_apply_apply]
  · rintro ⟨e,rfl⟩
    simp [selectedEnd]

theorem pushedVertex_set (s : NetworkShape n) (orientation : Fin s.edges → Bool) (d : K)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) (v : Fin s.vertices)
    (x : Fin (s.arity v) → Bool) :
    pushedVertex s orientation d f v x =
      d ^ (∑ i ∈ selectedAt s orientation v, if x i then 1 else 0 : ℕ) * f v x := by
  have he : (fun i => portScale s orientation d ⟨v,i⟩) =
      setWeights d (selectedAt s orientation v) := by
    funext i; simp [portScale, selectedAt, setWeights]
  rw [pushedVertex, gauge, he, weight_set]

/-- Reindexing the actual incidence bijection counts every selected endpoint once. -/
theorem product_port_weights (s : NetworkShape n) (orientation : Fin s.edges → Bool)
    (d : K) (x : Fin n → Bool) (z : (Fin s.edges × Bool) → Bool) :
    (∏ v, weight (fun i => portScale s orientation d ⟨v,i⟩) (s.assignment x z v)) =
      ∏ e, bitWeight d (z (e,orientation e)) := by
  classical
  let W : Fin n ⊕ (Fin s.edges × Bool) → K := Sum.elim (fun _ => 1)
    (fun eb => if eb.2 = orientation eb.1 then bitWeight d (z eb) else 1)
  have hw (p : Port s) : bitWeight (portScale s orientation d p) (s.assignment x z p.1 p.2) =
      W (s.ports p) := by
    cases hp : s.ports p with
    | inl i => simp [portScale, selectedEnd, NetworkShape.assignment, hp, W]
    | inr eb =>
      obtain ⟨e,b⟩ := eb
      by_cases hb : b = orientation e <;>
        simp [portScale, selectedEnd, NetworkShape.assignment, hp, W, hb]
  simp only [weight]
  rw [← Fintype.prod_sigma (fun p : Port s =>
    bitWeight (portScale s orientation d p) (s.assignment x z p.1 p.2))]
  simp_rw [hw]
  rw [s.ports.prod_comp]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [W, Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, one_mul]
  apply Finset.prod_congr rfl
  intro e he
  cases ho : orientation e <;> simp [ho]

/-- Full endpoint pushing in the literal finite network denotation. Loops and parallel
edges are permitted by the incidence bijection, with distinct endpoint occurrences. -/
theorem network_push (s : NetworkShape n) (orientation : Fin s.edges → Bool) (d : K)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) (E : Fin s.edges → Kernel K) :
    (Network.mk s f (fun e => weightedEdge d (orientation e) (E e))).denote =
      (Network.mk s (pushedVertex s orientation d f) E).denote := by
  funext x
  apply Finset.sum_congr rfl
  intro z hz
  simp only [weightedEdge_apply, pushedVertex, gauge]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [product_port_weights]
  have he : (∏ e, bitWeight d (if orientation e then z (e,true) else z (e,false))) =
      ∏ e, bitWeight d (z (e,orientation e)) := by
    apply Finset.prod_congr rfl
    intro e he; cases orientation e <;> rfl
  rw [he]
  ring

/-- The single joint parent tensor records every original vertex occurrence separately. -/
def jointParent (s : NetworkShape n) (f : (v : Fin s.vertices) → Signature K (s.arity v)) :
    Tensor K (Port s) := fun x => ∏ v, f v (fun i => x ⟨v,i⟩)

/-- Pushing on multiple copies is one fixed gauge on their joint parent tensor.
The theorem does not require, or infer, identical gauges on different copies. -/
theorem jointParent_push (s : NetworkShape n) (orientation : Fin s.edges → Bool) (d : K)
    (f : (v : Fin s.vertices) → Signature K (s.arity v)) :
    jointParent s (pushedVertex s orientation d f) =
      gauge (portScale s orientation d) (jointParent s f) := by
  funext x
  simp only [jointParent, pushedVertex, gauge, Finset.prod_mul_distrib]
  congr 1
  simp only [weight]
  rw [← Fintype.prod_sigma (fun p : Port s => bitWeight (portScale s orientation d p) (x p))]

/-- One fixed, incidence-computed gauged parent tuple works for the entire phase/product batch.
No equality of denotations or coherence certificate is an input hypothesis. -/
theorem batch_transport {Choice : Type*} (s : NetworkShape n)
    (orientation : Fin s.edges → Bool) (d : K)
    (f : (v : Fin s.vertices) → Signature K (s.arity v))
    (E : Choice → Fin s.edges → Kernel K) :
    ∀ choice, (Network.mk s f (fun e => weightedEdge d (orientation e) (E choice e))).denote =
      (Network.mk s (pushedVertex s orientation d f) (E choice)).denote :=
  fun choice => network_push s orientation d f (E choice)

end Holant.Marked.WeightedGauge
