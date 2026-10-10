import Holant.Proofs.Tetrahedral.CyclicResource.Networks


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant Holant.Certificates.FourthRootOdd
open Holant.LocalDrafts.MainChain.CyclicBoundary
noncomputable section
set_option backward.isDefEq.respectTransparency false

def occurrences (q : Signature ℂ 4) {n} (M : Network ℂ n) : ℕ := by
  classical
  exact ∑ v, if (⟨M.shape.arity v, M.vertex v⟩ : AnySignature ℂ) = ⟨4,q⟩ then 1 else 0

theorem occurrences_tensor (q : Signature ℂ 4) {m n}
    (L : Network ℂ m) (R : Network ℂ n) :
    occurrences q (L.tensor R) = occurrences q L + occurrences q R := by
  classical
  let f : Fin L.shape.vertices ⊕ Fin R.shape.vertices → ℕ := fun v =>
    if (⟨(Network.tensorFinite L R).arity v,
      (Network.tensorFinite L R).vertex v⟩ : AnySignature ℂ) = ⟨4,q⟩ then 1 else 0
  change (∑ v, f ((Fintype.equivFin
    (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)) = _
  rw [(Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm.sum_comp,
    Fintype.sum_sum_type]
  rfl

theorem occurrences_input (q : Signature ℂ 4) :
    occurrences q (singleVertexNetwork q) = 1 := by
  classical
  simp [occurrences,singleVertexNetwork]

/-- A source family excluding the original literal q gives a derived zero
cost; the hypothesis is about allowed labels, not about the desired count. -/
theorem occurrences_zero_of_labels (q : Signature ℂ 4) {n} (M : Network ℂ n)
    (S : SignatureFamily ℂ) (hq : (⟨4,q⟩ : AnySignature ℂ) ∉ S)
    (hM : ∀ v, (⟨M.shape.arity v,M.vertex v⟩ : AnySignature ℂ) ∈ S) :
    occurrences q M = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro v _
  have hne : (⟨M.shape.arity v,M.vertex v⟩ : AnySignature ℂ) ≠ ⟨4,q⟩ := by
    intro he
    exact hq (he ▸ hM v)
  simp [hne]

variable {ι : Type*} {q : Signature ℂ 4} {B : ι → Kernel ℂ}

def Circuit.expand (A : ι → Network ℂ 2) : {n : ℕ} → Circuit q B n → Network ℂ n
  | _, .input => singleVertexNetwork q
  | _, .auxiliary i => A i
  | _, .reorder C p => reorderNetwork (C.expand A) p
  | _, .tensor L R => (L.expand A).tensor (R.expand A)
  | _, .contract C => (C.expand A).contract Signature.disequality

def Circuit.auxCost (w : ι → ℕ) : {n : ℕ} → Circuit q B n → ℕ
  | _, .input => 0
  | _, .auxiliary i => w i
  | _, .reorder C _ => C.auxCost w
  | _, .tensor L R => L.auxCost w + R.auxCost w
  | _, .contract C => C.auxCost w

theorem Circuit.expanded_count {n} (C : Circuit q B n) (A : ι → Network ℂ 2) :
    occurrences q (C.expand A) = C.calls + C.auxCost (fun i => occurrences q (A i)) := by
  induction C with
  | input => simpa [expand,calls,auxCost] using occurrences_input q
  | auxiliary i => simp [expand,calls,auxCost]
  | reorder C p ih => exact ih
  | contract C ih => exact ih
  | tensor L R ihL ihR =>
    simp only [expand,occurrences_tensor,calls,auxCost,ihL,ihR]
    omega

theorem Circuit.auxCost_zero {n} (C : Circuit q B n) (w : ι → ℕ)
    (hw : ∀ i, w i = 0) : C.auxCost w = 0 := by
  induction C <;> simp_all [auxCost]

theorem Circuit.expand_denote {n} (C : Circuit q B n) (A : ι → Network ℂ 2)
    (hA : ∀ i, (A i).denote = PhysicalAttachments.binary (B i)) :
    (C.expand A).denote = C.network.denote := by
  induction C with
  | input => rfl
  | auxiliary i => exact (hA i).trans (singleVertexNetwork_denote _).symm
  | reorder C p ih => simpa only [expand,network,reorderNetwork_denote,ih]
  | contract C ih => simpa only [expand,network,Network.denote_contract,ih]
  | tensor L R ihL ihR =>
    simpa only [expand,network,Network.denote_tensor,ihL,ihR]

/-- These are actual ordinary auxiliary graphs, including all original
vertices, edge labels and boundary order. There is deliberately no size field.
Exact representatives already include their phase normalization scalars. -/
structure AuxiliaryExpansion (F : SignatureFamily ℂ) (B : ι → Kernel ℂ) where
  graph : ι → Network ℂ 2
  labels : ∀ i v, (⟨(graph i).shape.arity v,(graph i).vertex v⟩ : AnySignature ℂ) ∈ F
  native : ∀ i e, (graph i).edge e = Signature.disequality
  value : ∀ i, (graph i).denote = PhysicalAttachments.binary (B i)

theorem Circuit.expand_labels {n} (C : Circuit q B n) {F : SignatureFamily ℂ}
    (A : AuxiliaryExpansion F B) (hq : (⟨4,q⟩ : AnySignature ℂ) ∈ F) :
    ∀ v, (⟨(C.expand A.graph).shape.arity v,(C.expand A.graph).vertex v⟩ : AnySignature ℂ) ∈ F := by
  induction C with
  | input => intro v; exact hq
  | auxiliary i => exact A.labels i
  | reorder C p ih => exact ih
  | contract C ih => exact ih
  | tensor L R ihL ihR =>
    intro v
    change (⟨_,(Network.tensorFinite (L.expand A.graph) (R.expand A.graph)).vertex
      ((Fintype.equivFin (Fin (L.expand A.graph).shape.vertices ⊕
        Fin (R.expand A.graph).shape.vertices)).symm v)⟩ : AnySignature ℂ) ∈ F
    cases (Fintype.equivFin (Fin (L.expand A.graph).shape.vertices ⊕
      Fin (R.expand A.graph).shape.vertices)).symm v with
    | inl v => exact ihL v
    | inr v => exact ihR v

theorem Circuit.expand_native {n} (C : Circuit q B n) {F : SignatureFamily ℂ}
    (A : AuxiliaryExpansion F B) :
    ∀ e, (C.expand A.graph).edge e = Signature.disequality := by
  induction C with
  | input => intro e; exact Fin.elim0 e
  | auxiliary i => exact A.native i
  | reorder C p ih => exact ih
  | contract C ih => intro e; exact Fin.cases rfl ih e
  | tensor L R ihL ihR =>
    intro e
    change (Network.tensorFinite (L.expand A.graph) (R.expand A.graph)).edge
      ((Fintype.equivFin (Fin (L.expand A.graph).shape.edges ⊕
        Fin (R.expand A.graph).shape.edges)).symm e) = _
    cases (Fintype.equivFin (Fin (L.expand A.graph).shape.edges ⊕
      Fin (R.expand A.graph).shape.edges)).symm e with
    | inl e => exact ihL e
    | inr e => exact ihR e

/-- The same original-F graph witnesses both the exact resource equation and
the target equation. The original certificate scalar is not discarded. -/
theorem Certificate.expanded {n k} {f : Signature ℂ n} (W : Certificate q B f k)
    {F : SignatureFamily ℂ} (A : AuxiliaryExpansion F B)
    (hq : (⟨4,q⟩ : AnySignature ℂ) ∈ F) :
    Gadget.Realizes F .disequality (W.circuit.expand A.graph).denote ∧
    (W.circuit.expand A.graph).denote = W.scalar • f ∧
    occurrences q (W.circuit.expand A.graph) =
      k + W.circuit.auxCost (fun i => occurrences q (A.graph i)) := by
  refine ⟨Gadget.realizes_network _ F .disequality
    (W.circuit.expand_labels A hq) (W.circuit.expand_native A),?_,?_⟩
  · exact (W.circuit.expand_denote A.graph A.value).trans W.equation
  · rw [W.circuit.expanded_count,W.calls_eq]

/-- For a two-q template the expanded bound is equivalent to zero auxiliary
cost. This equivalence exposes the missing provenance instead of assuming it. -/
theorem Certificate.two_bound_iff {n} {f : Signature ℂ n} (W : Certificate q B f 2)
    (A : ι → Network ℂ 2) :
    occurrences q (W.circuit.expand A) ≤ 2 ↔
      W.circuit.auxCost (fun i => occurrences q (A i)) = 0 := by
  rw [W.circuit.expanded_count,W.calls_eq]
  omega

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
