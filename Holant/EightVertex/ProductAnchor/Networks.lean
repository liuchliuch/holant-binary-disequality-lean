import Holant.EightVertex.ProductAnchor.NetworksData

/-! The normalized equality-anchor gadgets from Lemma 4.2 are actual finite
ordinary equality-edge networks. Every vertex is exactly the original Fs,
including its original ordered ports. The odd-weight construction has a genuine
self-loop on the second copy; no free basis or replacement signature is used. -/
namespace Holant.EightVertex.ProductAnchor
open Holant Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

variable {K : Type*} [CommRing K]

/-- Connect the two internal pairs specified by the explicit incidence table. -/
def twoCopyNetwork (s : Word) (f : Signature K 4) : Network K 4 :=
  ((reorderNetwork (pairCorolla f) (wiringEquiv s).symm).contract
    Signature.equality).contract Signature.equality

/-- The one-or-two-copy graph with exactly the supplied normalized labels. -/
def normalizedNetwork (s : Word) : Network K 4 :=
  if weight s = 0 ∨ weight s = 4 then Network.corolla (normalized s)
  else twoCopyNetwork s (normalized s)

/-- Internal assignments are two independent bits, one per equality edge. -/
def internalPrefix (u v : Bool) (x : Word) : Fin 8 → Bool :=
  Fin.cons u (Fin.cons u (Fin.cons v (Fin.cons v x)))

def copyWord (s : Word) (v : Fin 2) (u w : Bool) (x : Word) : Word :=
  fun i => internalPrefix u w x ((wiringEquiv s).symm (copyPort v i))

def twoCopyValue (s : Word) (f : Signature K 4) (u v : Bool) (x : Word) : K :=
  f (copyWord s 0 u v x) * f (copyWord s 1 u v x)

theorem twoCopyNetwork_denote (s : Word) (f : Signature K 4) (x : Word) :
    (twoCopyNetwork s f).denote x =
      (twoCopyValue s f false false x + twoCopyValue s f true false x) +
      (twoCopyValue s f false true x + twoCopyValue s f true true x) := by
  rw [twoCopyNetwork,Network.denote_contract,Network.denote_contract,
    reorderNetwork_denote,pairCorolla_denote]
  simp only [Signature.contract_equality,Tensor.reindex_apply,Signature.tensor_apply]
  rfl

@[simp] theorem normalized_intCast (s x : Word) :
    ((normalized (K := ℤ) s x : ℤ) : K) = normalized s x := by
  simp [normalized]

@[simp] theorem equalityFour_intCast (x : Word) :
    ((equalityFour (K := ℤ) x : ℤ) : K) = equalityFour x := by
  simp [equalityFour]

@[simp] theorem outputScalar_intCast (s : Word) :
    ((outputScalar (K := ℤ) s : ℤ) : K) = outputScalar s := by
  simp [outputScalar]

@[simp] theorem twoCopyValue_intCast (s : Word) (u v : Bool) (x : Word) :
    ((twoCopyValue s (normalized (K := ℤ) s) u v x : ℤ) : K) =
      twoCopyValue s (normalized s) u v x := by
  simp only [twoCopyValue,Int.cast_mul,normalized_intCast]

/-- Kernel-checked finite integer certificate over all 16 original words and
all 16 ordered boundary words. -/
theorem twoCopyValue_sum_integer : ∀ s x : Word, ¬(weight s = 0 ∨ weight s = 4) →
    (twoCopyValue s (normalized (K := ℤ) s) false false x +
      twoCopyValue s (normalized s) true false x) +
    (twoCopyValue s (normalized s) false true x +
      twoCopyValue s (normalized s) true true x) = outputScalar s * equalityFour x := by
  decide

/-- Exact finite entry calculation, transported through the integer ring map;
this retains the sign and every loop factor over any commutative ring. -/
theorem twoCopyValue_sum (s : Word) (h : ¬(weight s = 0 ∨ weight s = 4)) (x : Word) :
    (twoCopyValue s (normalized (K := K) s) false false x +
      twoCopyValue s (normalized s) true false x) +
    (twoCopyValue s (normalized s) false true x +
      twoCopyValue s (normalized s) true true x) = outputScalar s * equalityFour x := by
  have hz := congrArg (fun a : ℤ => (a : K)) (twoCopyValue_sum_integer s x h)
  simpa only [Int.cast_add,Int.cast_mul,twoCopyValue_intCast,outputScalar_intCast,
    equalityFour_intCast] using hz

theorem normalized_eq_equality_of_endpoint (s : Word)
    (h : weight s = 0 ∨ weight s = 4) :
    normalized (K := K) s = equalityFour := by
  have hz : ∀ s : Word, weight s = 0 ∨ weight s = 4 →
      normalized (K := ℤ) s = equalityFour := by decide
  funext x
  have hc := congrArg (fun a : ℤ => (a : K)) (congrFun (hz s h) x)
  simpa only [normalized_intCast,equalityFour_intCast] using hc

theorem outputScalar_of_endpoint (s : Word) (h : weight s = 0 ∨ weight s = 4) :
    outputScalar (K := K) s = 1 := by
  rcases h with h | h <;> norm_num [outputScalar,h]

/-- Literal graph denotation: Eq4 in weights 0,2,4; minus Eq4 in weights 1,3. -/
theorem normalizedNetwork_denote (s : Word) :
    (normalizedNetwork (K := K) s).denote = fun x => outputScalar s * equalityFour x := by
  unfold normalizedNetwork
  split
  · rename_i h
    rw [Network.denote_corolla,normalized_eq_equality_of_endpoint s h,
      outputScalar_of_endpoint s h]
    simp
  · rename_i h
    funext x
    rw [twoCopyNetwork_denote]
    exact twoCopyValue_sum s h x

theorem normalizedNetwork_vertices (s : Word) :
    (normalizedNetwork (K := K) s).shape.vertices =
      if weight s = 0 ∨ weight s = 4 then 1 else 2 := by
  unfold normalizedNetwork
  split <;> rfl

theorem normalizedNetwork_vertices_le_two (s : Word) :
    (normalizedNetwork (K := K) s).shape.vertices ≤ 2 := by
  rw [normalizedNetwork_vertices]
  split <;> decide

/-- A dependent label condition packaged before case analysis of the graph. -/
def LabelsAre (N : Network K 4) (f : Signature K 4) : Prop :=
  ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature K) = ⟨4,f⟩

def EdgesAreEquality (N : Network K 4) : Prop :=
  ∀ e, N.edge e = Signature.equality

theorem normalizedNetwork_labels (s : Word) :
    LabelsAre (normalizedNetwork (K := K) s) (normalized s) := by
  unfold normalizedNetwork
  split <;> intro v <;> rfl

theorem normalizedNetwork_edges (s : Word) :
    EdgesAreEquality (normalizedNetwork (K := K) s) := by
  unfold normalizedNetwork
  split
  · intro e
    exact Fin.elim0 e
  · intro e
    change Fin 2 at e
    fin_cases e <;> rfl

/-- The same actual graph in the manuscript's full open-half-edge model. -/
def normalizedOpenNetwork (s : Word) : OpenNetwork K 4 :=
  (normalizedNetwork s).asOpen (fun _ => .equality)

theorem normalizedOpenNetwork_raw (s : Word) :
    (normalizedOpenNetwork (K := K) s).raw = fun x => outputScalar s * equalityFour x := by
  rw [normalizedOpenNetwork,Network.raw_asOpen]
  · exact normalizedNetwork_denote s
  · intro e
    exact (normalizedNetwork_edges s e).symm

theorem normalizedOpenNetwork_tensor (s : Word) :
    (normalizedOpenNetwork (K := K) s).tensor = fun x => outputScalar s * equalityFour x := by
  rw [normalizedOpenNetwork,Network.tensor_asOpen]
  · exact normalizedNetwork_denote s
  · intro e
    exact (normalizedNetwork_edges s e).symm

theorem normalizedOpenNetwork_vertices_le_two (s : Word) :
    (normalizedOpenNetwork (K := K) s).shape.vertices ≤ 2 :=
  normalizedNetwork_vertices_le_two s

theorem normalized_realizes (s : Word) :
    Gadget.Realizes ({⟨4,normalized (K := K) s⟩} : SignatureFamily K) .equality
      (fun x => outputScalar s * equalityFour x) := by
  rw [←normalizedNetwork_denote]
  apply Gadget.realizes_network
  · intro v
    rw [normalizedNetwork_labels s v]
    exact Set.mem_singleton _
  · exact normalizedNetwork_edges s

theorem outputScalar_ne_zero [Nontrivial K] (s : Word) : outputScalar (K := K) s ≠ 0 := by
  exact IsUnit.ne_zero (IsUnit.pow (weight s) isUnit_neg_one)

theorem normalized_realizesUpTo [Nontrivial K] (s : Word) :
    Gadget.RealizesUpTo ({⟨4,normalized (K := K) s⟩} : SignatureFamily K) .equality equalityFour :=
  ⟨outputScalar s,outputScalar_ne_zero s,normalized_realizes s⟩

end Holant.EightVertex.ProductAnchor
