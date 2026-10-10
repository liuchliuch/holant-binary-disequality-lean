import Holant.Marked.WeightedGauge.Network
import Holant.Marked.WeightedGauge.Traces

/-! Concrete fixed-incidence batches. Phase and product choices change literal
edge kernels; the original parent, incidence, orientations and external order are shared. -/
noncomputable section
namespace Holant.Marked.WeightedGauge
open scoped BigOperators
variable {K : Type*} [Field K]

/-- A single parent occurrence with every original slot accounted for by the explicit routing. -/
abbrev oneParentShape {N out edges : ℕ} (routing : Fin N ≃ (Fin out ⊕ (Fin edges × Bool))) :
    NetworkShape out where
  vertices := 1
  arity := fun _ => N
  edges := edges
  ports := {
    toFun := fun p => routing p.2
    invFun := fun p => ⟨0,routing.symm p⟩
    left_inv := by
      intro p
      obtain ⟨v,i⟩ := p
      have hv : v=0 := Fin.eq_zero v
      subst v; simp
    right_inv := by intro p; simp }

def parentNetwork {N out edges : ℕ} (routing : Fin N ≃ (Fin out ⊕ (Fin edges × Bool)))
    (h : Signature K N) (E : Fin edges → Kernel K) : Network K out :=
  ⟨oneParentShape routing, (fun _ => h), E⟩

def parentSet {N out edges : ℕ} (routing : Fin N ≃ (Fin out ⊕ (Fin edges × Bool)))
    (orientation : Fin edges → Bool) : Finset (Fin N) :=
  selectedAt (oneParentShape routing) orientation 0

/-- The very same explicitly computed gauged parent occurs in every member of the batch. -/
theorem one_parent_batch {N out edges : ℕ} {Choice : Type*}
    (routing : Fin N ≃ (Fin out ⊕ (Fin edges × Bool))) (orientation : Fin edges → Bool)
    (d : K) (h : Signature K N) (E : Choice → Fin edges → Kernel K) :
    ∀ choice, (parentNetwork routing h (fun e => weightedEdge d (orientation e) (E choice e))).denote =
      (parentNetwork routing (gauge (setWeights d (parentSet routing orientation)) h) (E choice)).denote := by
  intro choice
  have hh := network_push (oneParentShape routing) orientation d (fun _ => h) (E choice)
  refine hh.trans ?_
  apply Network.denote_congr
  · intro v x
    have hv : v=0 := Fin.eq_zero v
    subst v
    rw [pushedVertex_set]
    change d ^ (∑ i ∈ parentSet routing orientation, if x i then 1 else 0 : ℕ) * h x = _
    rw [gauge, weight_set]
  · intro e a b; rfl

def bitPair : Fin 2 ≃ (Fin 1 × Bool) where
  toFun i := (0, i = 1)
  invFun p := if p.2 then 1 else 0
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨i,b⟩ := p
    have hi : i=0 := Fin.eq_zero i
    subst i; cases b <;> rfl

/-- Canonical last-two-port contraction, followed by any stated original-port permutation. -/
def pairRouting (out : ℕ) (order : Equiv.Perm (Fin (out+2))) :
    Fin (out+2) ≃ (Fin out ⊕ (Fin 1 × Bool)) :=
  order.symm.trans (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) bitPair))

def pairBatch {out : ℕ} (d : K) (h : Signature K (out+2))
    (order : Equiv.Perm (Fin (out+2))) (p : Bool) (t : K) : Signature K out :=
  (parentNetwork (pairRouting out order) h (fun _ => effectiveKernel d p t)).denote

/-- E(t0), E(t1), O(t0), O(t1) are one concrete four-member batch on the same parent gauge. -/
theorem four_samples_coherent {out : ℕ} (d t0 t1 : K) (h : Signature K (out+2))
    (order : Equiv.Perm (Fin (out+2))) : ∀ choice : Bool × Bool,
    pairBatch d h order choice.1 (if choice.2 then t1 else t0) =
      (parentNetwork (pairRouting out order)
        (gauge (setWeights d (parentSet (pairRouting out order) (fun _ => false))) h)
        (fun _ => standardKernel choice.1 (if choice.2 then t1 else t0))).denote := by
  intro choice
  exact one_parent_batch (pairRouting out order) (fun _ => false) d h
    (fun (c : Bool × Bool) _ => standardKernel c.1 (if c.2 then t1 else t0)) choice

/-- The original six-port parent is fixed throughout its complete quaternary phase family. -/
theorem six_to_four_coherent (d : K) (h : Signature K 6) (order : Equiv.Perm (Fin 6))
    (p : Bool) : ∀ t : K, pairBatch d h order p t =
      (parentNetwork (pairRouting 4 order)
        (gauge (setWeights d (parentSet (pairRouting 4 order) (fun _ => false))) h)
        (fun _ => standardKernel p t)).denote := by
  intro t
  exact one_parent_batch (pairRouting 4 order) (fun _ => false) d h
    (fun t _ => standardKernel p t) t

/-- Two actual sampled products are compared using the same whole trace-cover skeleton.
The distinguished initial kernel selects the product; all later trace/fusion edges
and every original port occurrence remain fixed. -/
def traceCoverEdges {edges : ℕ} (initial : Fin edges) (K0 K1 : Kernel K)
    (rest : Fin edges → Kernel K) (choice : Bool) : Fin edges → Kernel K :=
  fun e => if e = initial then (if choice then K1 else K0) else rest e

theorem trace_cover_products_coherent {N out edges : ℕ}
    (routing : Fin N ≃ (Fin out ⊕ (Fin edges × Bool))) (orientation : Fin edges → Bool)
    (d : K) (h : Signature K N) (initial : Fin edges) (K0 K1 : Kernel K)
    (rest : Fin edges → Kernel K) : ∀ choice : Bool,
    (parentNetwork routing h (fun e => weightedEdge d (orientation e)
      (traceCoverEdges initial K0 K1 rest choice e))).denote =
      (parentNetwork routing (gauge (setWeights d (parentSet routing orientation)) h)
        (traceCoverEdges initial K0 K1 rest choice)).denote :=
  one_parent_batch routing orientation d h (traceCoverEdges initial K0 K1 rest)

end Holant.Marked.WeightedGauge
