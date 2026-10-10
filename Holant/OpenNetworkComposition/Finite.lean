import Holant.Realization
import Mathlib.Logic.Equiv.Fin.Basic

/-! Finite-index presentation of the existing full OpenNetwork semantics.
This changes index types only; ordinary/free boundary rules, edge kinds, and
boundary correction are retained literally. No composition closure is assumed. -/
noncomputable section
namespace Holant.OpenNetworkComposition

abbrev Ports (V F : Type*) (arity : V → ℕ) := (Σ v : V,Fin (arity v)) ⊕ F

structure FiniteShape (V F E : Type*) (n : ℕ) where
  arity : V → ℕ
  boundary : Fin n ↪ Ports V F arity
  ends : E × Bool ↪ Ports V F arity
  ordinary_boundary_iff_unpaired : ∀ p : Σ v : V,Fin (arity v),
    (∃ j,boundary j=Sum.inl p) ↔ ¬∃ e,ends e=Sum.inl p
  freeBoundary : F → Fin n
  free_boundary : ∀ f,boundary (freeBoundary f)=Sum.inr f
  freeEdge : F → E × Bool
  free_paired : ∀ f,ends (freeEdge f)=Sum.inr f

structure FiniteNetwork (K V F E : Type*) (n : ℕ) where
  shape : FiniteShape V F E n
  vertex : (v : V) → Signature K (shape.arity v)
  edge : E → EdgeKind

namespace FiniteNetwork
variable {K V F E : Type*} {n : ℕ}

def ofOpen (N : OpenNetwork K n) :
    FiniteNetwork K (Fin N.shape.vertices) (Fin N.shape.free) (Fin N.shape.edges) n where
  shape := {
    arity := N.shape.arity
    boundary := N.shape.boundary
    ends := N.shape.ends
    ordinary_boundary_iff_unpaired := N.shape.ordinary_boundary_iff_unpaired
    freeBoundary := N.shape.freeBoundary
    free_boundary := N.shape.free_boundary
    freeEdge := N.shape.freeEdge
    free_paired := N.shape.free_paired }
  vertex := N.vertex
  edge := N.edge

variable [Fintype V] [Fintype F] [Fintype E]

def weight [CommSemiring K] (N : FiniteNetwork K V F E n) (z : Ports V F N.shape.arity → Bool) : K :=
  (∏ v,N.vertex v (fun i => z (.inl ⟨v,i⟩)))*∏ e,(N.edge e).value (z (N.shape.ends (e,false))) (z (N.shape.ends (e,true)))

def raw [CommSemiring K] (N : FiniteNetwork K V F E n) : Signature K n := by
  classical
  exact fun x => ∑ z : Ports V F N.shape.arity → Bool,
    if ∀ j,z (N.shape.boundary j)=x j then N.weight z else 0

def boundaryKernel [CommSemiring K] (N : FiniteNetwork K V F E n) (j : Fin n) : Kernel K :=
  match N.shape.boundary j with
  | .inl _ => Signature.equality
  | .inr f => (N.edge (N.shape.freeEdge f).1).value

def tensor [CommSemiring K] (N : FiniteNetwork K V F E n) : Signature K n :=
  Signature.coordinateAction N.boundaryKernel N.raw

/-- Explicit port transport, preserving local vertex coordinates and free stubs. -/
def portEquiv (N : FiniteNetwork K V F E n) :
    OpenPorts (Fintype.card V) (fun v => N.shape.arity ((Fintype.equivFin V).symm v)) (Fintype.card F) ≃
      Ports V F N.shape.arity :=
  Equiv.sumCongr (Equiv.sigmaCongrLeft (β := fun v : V => Fin (N.shape.arity v)) (Fintype.equivFin V).symm) (Fintype.equivFin F).symm

def edgeEquiv : (Fin (Fintype.card E) × Bool) ≃ (E × Bool) :=
  Equiv.prodCongr (Fintype.equivFin E).symm (Equiv.refl Bool)

set_option backward.isDefEq.respectTransparency false in
/-- Enumerate the finite types into the repository's exact OpenNetwork carrier. -/
def toOpen (N : FiniteNetwork K V F E n) : OpenNetwork K n where
  shape := {
    vertices := Fintype.card V
    arity := fun v => N.shape.arity ((Fintype.equivFin V).symm v)
    free := Fintype.card F
    edges := Fintype.card E
    boundary := N.shape.boundary.trans N.portEquiv.symm.toEmbedding
    ends := edgeEquiv.toEmbedding.trans (N.shape.ends.trans N.portEquiv.symm.toEmbedding)
    ordinary_boundary_iff_unpaired := by
      intro p
      have hs := N.shape.ordinary_boundary_iff_unpaired ((Equiv.sigmaCongrLeft (β := fun v : V => Fin (N.shape.arity v)) (Fintype.equivFin V).symm) p)
      constructor
      · rintro ⟨j,hj⟩ ⟨e,he⟩
        apply hs.mp ⟨j,?_⟩ ⟨edgeEquiv e,?_⟩
        · have h := congrArg N.portEquiv hj
          simpa [portEquiv] using h
        · have h := congrArg N.portEquiv he
          simpa [portEquiv] using h
      · intro hn
        have hp : ¬∃ e,N.shape.ends e=Sum.inl ((Equiv.sigmaCongrLeft (β := fun v : V => Fin (N.shape.arity v)) (Fintype.equivFin V).symm) p) := by
          rintro ⟨e,he⟩
          apply hn
          refine ⟨edgeEquiv.symm e,?_⟩
          apply N.portEquiv.injective
          simpa [portEquiv] using he
        obtain ⟨j,hj⟩ := hs.mpr hp
        refine ⟨j,?_⟩
        apply N.portEquiv.injective
        simpa [portEquiv] using hj
    freeBoundary := fun f => N.shape.freeBoundary ((Fintype.equivFin F).symm f)
    free_boundary := by
      intro f
      apply N.portEquiv.injective
      simpa [portEquiv] using N.shape.free_boundary ((Fintype.equivFin F).symm f)
    freeEdge := fun f => edgeEquiv.symm (N.shape.freeEdge ((Fintype.equivFin F).symm f))
    free_paired := by
      intro f
      apply N.portEquiv.injective
      simpa [portEquiv] using N.shape.free_paired ((Fintype.equivFin F).symm f) }
  vertex := fun v => N.vertex ((Fintype.equivFin V).symm v)
  edge := fun e => N.edge ((Fintype.equivFin E).symm e)

end FiniteNetwork
end Holant.OpenNetworkComposition
