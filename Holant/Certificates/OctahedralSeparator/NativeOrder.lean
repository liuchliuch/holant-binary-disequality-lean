import Holant.Certificates.OctahedralSeparator.NativeSparse

/-! Local vertex-port reorderings preserve actual network denotation.  Applied
to the native separator graphs, they keep the literal original ancestor as the
one six-port resource while selecting any ordered original pair. -/
namespace Holant.Certificates.OctahedralSeparator.Native
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Reorder each vertex's incident ports and inversely reorder its label. -/
def reorderVertexPorts {R : Type*} {n : ℕ} (N : Network R n)
    (e : (v : Fin N.shape.vertices) → Equiv.Perm (Fin (N.shape.arity v))) : Network R n where
  shape := {
    vertices := N.shape.vertices
    arity := N.shape.arity
    edges := N.shape.edges
    ports := (Equiv.sigmaCongrRight e).trans N.shape.ports }
  vertex := fun v => Tensor.reindex (e v).symm (N.vertex v)
  edge := N.edge

theorem reorderVertexPorts_denote {R : Type*} [CommSemiring R] {n : ℕ}
    (N : Network R n) (e : (v : Fin N.shape.vertices) → Equiv.Perm (Fin (N.shape.arity v))) :
    (reorderVertexPorts N e).denote = N.denote := by
  funext x
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun a => a * ∏ i : Fin N.shape.edges, N.edge i (z (i,false)) (z (i,true)))
  apply Finset.prod_congr rfl
  intro v _
  simp [reorderVertexPorts,Tensor.reindex,NetworkShape.assignment]
  rfl

/-- Only the six-port ancestor's local port order changes. -/
def dressedOrder (p : Equiv.Perm (Fin 6)) : (v : Fin 6) → Equiv.Perm (Fin (dressedArity v)) :=
  Fin.cases p (fun _ => Equiv.refl _)

def orderedDressedNetwork (p : Equiv.Perm (Fin 6)) (h : Signature ℂ 6)
    (K : Binary) (L : Fin 4 → Binary) : Network ℂ 4 :=
  reorderVertexPorts (dressedNetwork (Tensor.reindex p h) K L) (dressedOrder p)

theorem orderedDressedNetwork_denote (p : Equiv.Perm (Fin 6)) (h : Signature ℂ 6)
    (K : Binary) (L : Fin 4 → Binary) :
    (orderedDressedNetwork p h K L).denote =
      Signature.coordinateAction L (Signature.contract K (Tensor.reindex p h)) := by
  rw [orderedDressedNetwork,reorderVertexPorts_denote,dressedNetwork_denote]

theorem orderedDressedNetwork_ancestor (p : Equiv.Perm (Fin 6)) (h : Signature ℂ 6)
    (K : Binary) (L : Fin 4 → Binary) :
    (orderedDressedNetwork p h K L).vertex (0 : Fin 6) = h := by
  change Tensor.reindex p.symm (Tensor.reindex p h) = h
  exact Tensor.reindex_symm p h

theorem ordered_dressed_realizes (p : Equiv.Perm (Fin 6)) (h : Signature ℂ 6)
    (K : Binary) (L : Fin 4 → Binary) :
    Gadget.Realizes (dressedResources h K L) .disequality
      (Signature.coordinateAction L (Signature.contract K (Tensor.reindex p h))) := by
  have hr := Gadget.realizes_network (orderedDressedNetwork p h K L) (dressedResources h K L)
    .disequality (by
      intro v
      fin_cases v
      · change (⟨6,(orderedDressedNetwork p h K L).vertex (0 : Fin 6)⟩ : AnySignature ℂ) ∈ _
        rw [orderedDressedNetwork_ancestor]
        exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨0,rfl⟩)
      · exact Or.inr (Or.inr ⟨1,rfl⟩)
      · exact Or.inr (Or.inr ⟨2,rfl⟩)
      · exact Or.inr (Or.inr ⟨3,rfl⟩))
    (by intro i; rfl)
  rwa [orderedDressedNetwork_denote] at hr

theorem ordered_dressed_realizes_of_mem (F : SignatureFamily ℂ) (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ F)
    (hK : (⟨2,binarySignature (pairVertex K)⟩ : AnySignature ℂ) ∈ F)
    (hL : ∀ j, (⟨2,binarySignature (legVertex (L j))⟩ : AnySignature ℂ) ∈ F) :
    Gadget.Realizes F .disequality
      (Signature.coordinateAction L (Signature.contract K (Tensor.reindex p h))) := by
  apply (ordered_dressed_realizes p h K L).mono
  rintro q (rfl | rfl | ⟨j,rfl⟩)
  · exact hh
  · exact hK
  · exact hL j

@[simp] theorem orderedDressedNetwork_vertices (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) :
    (orderedDressedNetwork p h K L).shape.vertices = 6 := rfl

@[simp] theorem orderedDressedNetwork_edges (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) :
    (orderedDressedNetwork p h K L).shape.edges = 6 := rfl

@[simp] theorem orderedDressedNetwork_binary_vertices (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) :
    (Finset.univ.filter (fun v => (orderedDressedNetwork p h K L).shape.arity v = 2)).card = 5 := by
  change (Finset.univ.filter (fun v : Fin 6 => dressedArity v = 2)).card = 5
  decide

@[simp] theorem orderedDressedNetwork_ancestor_vertices (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) :
    (Finset.univ.filter (fun v => (orderedDressedNetwork p h K L).shape.arity v = 6)).card = 1 := by
  change (Finset.univ.filter (fun v : Fin 6 => dressedArity v = 6)).card = 1
  decide

/-- The sparse graph likewise changes no binary vertex or native edge. -/
def sparseOrder (p : Equiv.Perm (Fin 6)) : (v : Fin 5) → Equiv.Perm (Fin (sparseArity v)) :=
  Fin.cases p (fun _ => Equiv.refl _)

def orderedSparseNetwork (p : Equiv.Perm (Fin 6)) (h : Signature ℂ 6)
    (K L1 L3 M : Binary) : Network ℂ 2 :=
  reorderVertexPorts (sparseNetwork (Tensor.reindex p h) K L1 L3 M) (sparseOrder p)

theorem orderedSparseNetwork_denote (p : Equiv.Perm (Fin 6)) (h : Signature ℂ 6)
    (K L1 L3 M : Binary) :
    (orderedSparseNetwork p h K L1 L3 M).denote = Signature.contract M
      (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3]
        (Signature.contract K (Tensor.reindex p h))) := by
  rw [orderedSparseNetwork,reorderVertexPorts_denote,sparseNetwork_denote]

theorem orderedSparseNetwork_ancestor (p : Equiv.Perm (Fin 6)) (h : Signature ℂ 6)
    (K L1 L3 M : Binary) :
    (orderedSparseNetwork p h K L1 L3 M).vertex (0 : Fin 5) = h := by
  change Tensor.reindex p.symm (Tensor.reindex p h) = h
  exact Tensor.reindex_symm p h

theorem ordered_sparse_realizes (p : Equiv.Perm (Fin 6)) (h : Signature ℂ 6)
    (K L1 L3 M : Binary) :
    Gadget.Realizes (sparseResources h K L1 L3 M) .disequality
      (Signature.contract M
        (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3]
          (Signature.contract K (Tensor.reindex p h)))) := by
  have hr := Gadget.realizes_network (orderedSparseNetwork p h K L1 L3 M)
    (sparseResources h K L1 L3 M) .disequality (by
      intro v
      fin_cases v
      · change (⟨6,(orderedSparseNetwork p h K L1 L3 M).vertex (0 : Fin 5)⟩ : AnySignature ℂ) ∈ _
        rw [orderedSparseNetwork_ancestor]
        exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by intro i; rfl)
  rwa [orderedSparseNetwork_denote] at hr

theorem ordered_sparse_realizes_of_mem (F : SignatureFamily ℂ) (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K L1 L3 M : Binary)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ F)
    (hK : (⟨2,binarySignature (pairVertex K)⟩ : AnySignature ℂ) ∈ F)
    (hL1 : (⟨2,binarySignature (legVertex L1)⟩ : AnySignature ℂ) ∈ F)
    (hL3 : (⟨2,binarySignature (legVertex L3)⟩ : AnySignature ℂ) ∈ F)
    (hM : (⟨2,binarySignature (pairVertex M)⟩ : AnySignature ℂ) ∈ F) :
    Gadget.Realizes F .disequality
      (Signature.contract M
        (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3]
          (Signature.contract K (Tensor.reindex p h)))) := by
  apply (ordered_sparse_realizes p h K L1 L3 M).mono
  rintro q (rfl | rfl | rfl | rfl | rfl)
  · exact hh
  · exact hK
  · exact hL1
  · exact hL3
  · exact hM

@[simp] theorem orderedSparseNetwork_vertices (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (orderedSparseNetwork p h K L1 L3 M).shape.vertices = 5 := rfl

@[simp] theorem orderedSparseNetwork_edges (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (orderedSparseNetwork p h K L1 L3 M).shape.edges = 6 := rfl

@[simp] theorem orderedSparseNetwork_binary_vertices (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (Finset.univ.filter (fun v => (orderedSparseNetwork p h K L1 L3 M).shape.arity v = 2)).card = 4 := by
  change (Finset.univ.filter (fun v : Fin 5 => sparseArity v = 2)).card = 4
  decide

@[simp] theorem orderedSparseNetwork_ancestor_vertices (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (Finset.univ.filter (fun v => (orderedSparseNetwork p h K L1 L3 M).shape.arity v = 6)).card = 1 := by
  change (Finset.univ.filter (fun v : Fin 5 => sparseArity v = 6)).card = 1
  decide

/-- With the source's swap, the initial native pair uses original ports1/3. -/
theorem orderedDressedNetwork_original_pair (h : Signature ℂ 6)
    (K : Binary) (L : Fin 4 → Binary) :
    (orderedDressedNetwork TetrahedralOrientation.contractOrder h K L).shape.ports
        ⟨(0 : Fin 6),(0 : Fin 6)⟩ = .inr ((0 : Fin 6),false) ∧
    (orderedDressedNetwork TetrahedralOrientation.contractOrder h K L).shape.ports
        ⟨(0 : Fin 6),(2 : Fin 6)⟩ = .inr ((1 : Fin 6),false) := by
  exact ⟨rfl,rfl⟩

theorem orderedSparseNetwork_original_pair (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (orderedSparseNetwork TetrahedralOrientation.contractOrder h K L1 L3 M).shape.ports
        ⟨(0 : Fin 5),(0 : Fin 6)⟩ = .inr ((0 : Fin 6),false) ∧
    (orderedSparseNetwork TetrahedralOrientation.contractOrder h K L1 L3 M).shape.ports
        ⟨(0 : Fin 5),(2 : Fin 6)⟩ = .inr ((1 : Fin 6),false) := by
  exact ⟨rfl,rfl⟩

@[simp] theorem orderedDressedNetwork_native_edge (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) (i : Fin 6) :
    (orderedDressedNetwork p h K L).edge i = Signature.disequality := rfl

@[simp] theorem orderedSparseNetwork_native_edge (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K L1 L3 M : Binary) (i : Fin 6) :
    (orderedSparseNetwork p h K L1 L3 M).edge i = Signature.disequality := rfl

end
end Holant.Certificates.OctahedralSeparator.Native
