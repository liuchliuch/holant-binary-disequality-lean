import Holant.Observability.Chains
import Holant.NetworkTensor
import Holant.NetworkContraction

/-!
Actual graph provenance for every finite chain in the source span. Reindexing,
disjoint union, and contraction preserve all supplied vertices and all old
edges. The exchange link is implemented by two supplied literal I vertices
and one native X edge, so X is not assumed as an extra vertex resource.
-/

namespace Holant.Observability

noncomputable section

/-- Read an ordered binary table as an ordinary two-port signature. -/
def binarySignature (B : Mat) : Signature ℂ 2 := fun x => B (x 0) (x 1)

/-- Change only the names of the exposed boundary occurrences. -/
def reindexNetwork {n : ℕ} (N : Network ℂ n) (e : Equiv.Perm (Fin n)) : Network ℂ n where
  shape := {
    vertices := N.shape.vertices
    arity := N.shape.arity
    edges := N.shape.edges
    ports := N.shape.ports.trans (Equiv.sumCongr e (Equiv.refl _)) }
  vertex := N.vertex
  edge := N.edge

theorem reindexNetwork_denote {n : ℕ} (N : Network ℂ n) (e : Equiv.Perm (Fin n)) :
    (reindexNetwork N e).denote = Tensor.reindex e N.denote := by
  funext x
  unfold Network.denote Tensor.reindex
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext i
  dsimp [NetworkShape.assignment, reindexNetwork]
  cases N.shape.ports ⟨v, i⟩ <;> rfl

/-- Old boundary `[L0,L1,R0,R1]` becomes `[L1,R0,L0,R1]`. -/
def seriesOrder : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide
  right_inv := by decide

/-- A genuine graph joining left port one to right port zero by native X. -/
def seriesNetwork (L R : Network ℂ 2) : Network ℂ 2 :=
  (reindexNetwork (L.tensor R) seriesOrder).contract Signature.disequality

/-- Exact denotation of graph series, including all old graph summations. -/
theorem seriesNetwork_denote (L R : Network ℂ 2) (A B : Mat)
    (hL : L.denote = binarySignature A) (hR : R.denote = binarySignature B) :
    (seriesNetwork L R).denote =
      binarySignature (Kernel.join Signature.disequality A (Kernel.transpose B)) := by
  rw [seriesNetwork, Network.denote_contract, reindexNetwork_denote,
    Network.denote_tensor, hL, hR]
  funext x
  change (∑ a : Bool, ∑ b : Bool,
    Signature.disequality a b * (A (x 0) a * B b (x 1))) =
    ∑ a : Bool, ∑ b : Bool, Signature.disequality a b * A (x 0) a * B b (x 1)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring


/-- Explicit reversal of the two external ports, retaining the same graph. -/
def reverseNetwork (N : Network ℂ 2) : Network ℂ 2 :=
  reindexNetwork N (Equiv.swap 0 1)

theorem reverseNetwork_denote (N : Network ℂ 2) (A : Mat)
    (hN : N.denote = binarySignature A) :
    (reverseNetwork N).denote = binarySignature (Kernel.transpose A) := by
  rw [reverseNetwork, reindexNetwork_denote, hN]
  funext x
  simp [Tensor.reindex, binarySignature, Kernel.transpose]

/-- Vertex-resource condition, using the existing dependent signature family. -/
def uses {n : ℕ} (N : Network ℂ n) (F : SignatureFamily ℂ) : Prop :=
  ∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature ℂ) ∈ F

/-- Every internal edge is the literal native X kernel. -/
def native {n : ℕ} (N : Network ℂ n) : Prop :=
  ∀ e, N.edge e = (Signature.disequality : Mat)

theorem seriesNetwork_uses (L R : Network ℂ 2) (F : SignatureFamily ℂ)
    (hL : uses L F) (hR : uses R F) : uses (seriesNetwork L R) F := by
  intro v
  change (⟨_, (Network.tensorFinite L R).vertex
    ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ :
      AnySignature ℂ) ∈ F
  cases (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
  | inl v => exact hL v
  | inr v => exact hR v

theorem seriesNetwork_native (L R : Network ℂ 2)
    (hL : native L) (hR : native R) : native (seriesNetwork L R) := by
  intro e
  refine Fin.cases ?_ (fun e => ?_) e
  · rfl
  · change (Network.tensorFinite L R).edge
      ((Fintype.equivFin (Fin L.shape.edges ⊕ Fin R.shape.edges)).symm e) = _
    cases (Fintype.equivFin (Fin L.shape.edges ⊕ Fin R.shape.edges)).symm e with
    | inl e => exact hL e
    | inr e => exact hR e

variable {ι : Type*}

/-- Only fixed actual input tables and the expressly available literal I.
The native X wire adds no extra vertex resource. -/
def chainResources (family : ι → Mat) : SignatureFamily ℂ :=
  insert ⟨2, binarySignature Signature.equality⟩
    (Set.range fun i => (⟨2, binarySignature (family i)⟩ : AnySignature ℂ))

namespace Chain

/-- Flatten the entire finite chain to an actual network using only native
X edges. This recursive graph construction contains no realization premise. -/
def network (family : ι → Mat) : Chain ι → Network ℂ 2
  | .atom i => Network.corolla (binarySignature (family i))
  | .identity => Network.corolla (binarySignature Signature.equality)
  | .exchange => seriesNetwork (Network.corolla (binarySignature Signature.equality))
      (Network.corolla (binarySignature Signature.equality))
  | .series L R => seriesNetwork (network family L) (network family R)
  | .reverse C => reverseNetwork (network family C)

/-- Every syntax node denotes exactly its actual flattened graph. -/
theorem network_denote (family : ι → Mat) (chain : Chain ι) :
    (network family chain).denote = binarySignature (evaluate family chain) := by
  induction chain with
  | atom i => exact Network.denote_corolla _
  | identity => exact Network.denote_corolla _
  | exchange =>
    rw [network, seriesNetwork_denote _ _ _ _ (Network.denote_corolla _)
      (Network.denote_corolla _)]
    simp only [Kernel.join_eq_mul, Kernel.transpose_equality, Kernel.equality_mul,
      Kernel.mul_equality, evaluate_exchange]
  | series L R hL hR => exact seriesNetwork_denote _ _ _ _ hL hR
  | reverse C hC => exact reverseNetwork_denote _ _ hC

/-- The graph's vertices have actual fixed provenance; series and reversal
never relabel or manufacture a binary vertex. -/
theorem network_uses (family : ι → Mat) (chain : Chain ι) :
    uses (network family chain) (chainResources family) := by
  have hI : uses (Network.corolla (binarySignature (Signature.equality : Mat)))
      (chainResources family) := fun _ => Set.mem_insert _ _
  induction chain with
  | atom i => exact fun _ => Set.mem_insert_of_mem _ ⟨i, rfl⟩
  | identity => exact hI
  | exchange => exact seriesNetwork_uses _ _ _ hI hI
  | series L R hL hR => exact seriesNetwork_uses _ _ _ hL hR
  | reverse C hC => exact hC

/-- All genuine internal edges are native X, including those added by series. -/
theorem network_native (family : ι → Mat) (chain : Chain ι) :
    native (network family chain) := by
  have hc (A : Mat) : native (Network.corolla (binarySignature A)) :=
    fun e => Fin.elim0 e
  induction chain with
  | atom i => exact hc _
  | identity => exact hc _
  | exchange => exact seriesNetwork_native _ _ (hc _) (hc _)
  | series L R hL hR => exact seriesNetwork_native _ _ hL hR
  | reverse C hC => exact hC

/-- An actual finite open gadget, with exact port order and literal scalars,
realizes every physical chain table using only the fixed supplied binaries
and literal I, on native X edges. -/
theorem realizes (family : ι → Mat) (chain : Chain ι) :
    Gadget.Realizes (chainResources family) .disequality
      (binarySignature (evaluate family chain)) := by
  rw [← network_denote]
  exact Gadget.realizes_network _ _ _ (network_uses family chain) (network_native family chain)

/-- Each transfer used to generate the source span is itself an actual
native-X gadget, with the appended I link recorded explicitly. -/
theorem realizes_transfer (family : ι → Mat) (chain : Chain ι) :
    Gadget.Realizes (chainResources family) .disequality
      (binarySignature (transfer family chain)) := by
  rw [← evaluate_append_identity]
  exact realizes family (.series chain .identity)

end Chain

end
end Holant.Observability
