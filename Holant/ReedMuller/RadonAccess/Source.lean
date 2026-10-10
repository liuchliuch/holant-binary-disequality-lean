import Holant.ReedMuller.RadonAccess.PairCoordinates
import Holant.ReedMuller.RadonAccess.NativeNetwork

/-! Source Lemma 7.15: actual accessible directions, their literal orthogonal
matrix, genuine affine quotient coordinates and a bounded one-copy Radon graph. -/
namespace Holant.ReedMuller.RadonAccess
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork GenerationNetwork
open Holant.Dihedral.CompatibleClosure
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def radonFamily (g : Signature ℂ (n+2)) : SignatureFamily ℂ := {f |
  f=⟨n+2,g⟩ ∨ f=⟨2,fun x => Signature.equality (x 0) (x 1)⟩ ∨
    f=⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ ∨ f=⟨8,rmCore⟩}

def boundaryRadon (F : RadonFrame (n+2)) (epsilon : ZMod 2)
    (g : Signature ℂ (n+2)) : Signature ℂ n := fun x =>
  F.radon epsilon (fun z => g (wordVector z))
    (F.iota epsilon (F.pairBoundaryLinearEquiv.symm (vectorWord x)))

/-- The literal one-copy constructor and every actual resource and boundary
coordinate are recorded. Its linear size bound is stronger than the source's
quadratic bound; no arithmetic-runtime claim is made. -/
theorem source_accessible_radon (g : Signature ℂ (n+2)) (v : BinaryVector (n+2))
    (hv : Accessible v) :
    ∃ (p : GenerationProgram (n+2)) (F : RadonFrame (n+2)),
      F.A=p.orthogonalMap ∧ F.v=v ∧ p.length≤n+2 ∧
      F.A.matrix.transpose*F.A.matrix=1 ∧
      F.A.matrix.transpose.mulVec (unitWord F.i+unitWord F.j)=v ∧
      ∀ epsilon : ZMod 2,∃ N : Network ℂ n,
        N=pairNetwork p g (pairOrder F.i F.j) epsilon ∧
        Uses (radonFamily g) N ∧ EdgesIX N ∧
        N.denote=boundaryRadon F epsilon g ∧
        N.shape.vertices≤n+3 ∧ N.shape.edges≤4*(n+2)+1 := by
  obtain ⟨p,i,j,hij,hlen,hbound,hmap,htranspose⟩ := accessible_coordinate_map v hv
  let F : RadonFrame (n+2) := ⟨p.orthogonalMap,i,j,hij⟩
  have hFv : F.v=v := by
    change p.orthogonalMap.symm (unitWord i+unitWord j)=v
    rw [←hmap,p.orthogonalMap.symm_apply_apply]
  refine ⟨p,F,rfl,hFv,hbound,F.A.transpose_mul, htranspose,?_⟩
  intro epsilon
  refine ⟨pairNetwork p g (pairOrder F.i F.j) epsilon,rfl,?_,
    pairNetwork_edges p g _ epsilon,pairNetwork_denote_radon p F rfl epsilon g,?_,?_⟩
  · exact pairNetwork_uses (radonFamily g) p g _ epsilon (Or.inl rfl)
      (Or.inr (Or.inr (Or.inr rfl)))
  · have H := pairNetwork_vertices p g (pairOrder F.i F.j) epsilon
    omega
  · have H := pairNetwork_edge_bound p g (pairOrder F.i F.j) epsilon
    omega

/-- The same actual one-copy construction has a native-X gadget realization.
Uniform subdivision inserts only the explicitly allowed I/X vertices. -/
theorem source_accessible_radon_native (g : Signature ℂ (n+2)) (v : BinaryVector (n+2))
    (hv : Accessible v) :
    ∃ (p : GenerationProgram (n+2)) (F : RadonFrame (n+2)),
      F.A=p.orthogonalMap ∧ F.v=v ∧
      ∀ epsilon : ZMod 2,∃ N : Network ℂ n,
        N=native (pairNetwork p g (pairOrder F.i F.j) epsilon) ∧
        Uses (radonFamily g) N ∧ (∀ e,N.edge e=Signature.disequality) ∧
        N.denote=boundaryRadon F epsilon g ∧
        N.shape.vertices≤5*(n+2)+2 ∧ N.shape.edges≤8*(n+2)+2 ∧
        Gadget.Realizes (radonFamily g) .disequality (boundaryRadon F epsilon g) := by
  obtain ⟨p,F,hA,hv,hp,_,_,h⟩ := source_accessible_radon g v hv
  refine ⟨p,F,hA,hv,?_⟩
  intro epsilon
  obtain ⟨N,rfl,hU,hE,hD,hV,hEdges⟩ := h epsilon
  have hI : (⟨2,fun x => Signature.equality (x 0) (x 1)⟩ : AnySignature ℂ)∈radonFamily g :=
    Or.inr (Or.inl rfl)
  have hX : (⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ : AnySignature ℂ)∈radonFamily g :=
    Or.inr (Or.inr (Or.inl rfl))
  refine ⟨native (pairNetwork p g (pairOrder F.i F.j) epsilon),rfl,
    uses_native _ _ hU hE hI hX,native_edge _,?_,?_,?_,?_⟩
  · rw [native_denote_of_edges _ hE,hD]
  · rw [native_vertices]
    omega
  · rw [native_edges]
    omega
  · rw [←hD]
    exact realizes_native_of_uses _ _ hU hE hI hX

/-- Necessity is the full orthogonal orbit characterization, not merely a
restriction imposed by the chosen circuit syntax. -/
theorem source_accessible_directions_exact (hn : 2≤n) (v : BinaryVector (n+2)) :
    (dot (ones (n+2)) v=0 ∧ v≠0 ∧ v≠ones (n+2)) ↔
      ∃ (A : OrthogonalMap (n+2)) (i j : Fin (n+2)), i≠j ∧ A v=unitWord i+unitWord j :=
  accessible_iff_orthogonal_pair (by omega) v

end
end Holant.ReedMuller.RadonAccess
