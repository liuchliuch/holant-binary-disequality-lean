import Holant.ReedMuller.AffineRadon.Overlap
import Holant.ReedMuller.AffineRadon.PhaseSource
import Holant.ReedMuller.AffineRadon.AccessibleTriple
import Holant.ReedMuller.AffineRadon.SpaceGeometryAvoidance

/-! A fixed actual orthogonal frame may be chosen for each accessible
original direction. All conditions concern its literal quotient card values,
not all possible coordinate choices or freely available basis gadgets. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 def FlatRadonCards (g : BinaryVector n → ℂ) : Prop :=
  ∀ v : BinaryVector n,Accessible v → ∃ F : RadonAccess.RadonFrame n,F.v=v ∧
    ∀ ε,FlatOrZero (fun x => RadonFrame.actualRadon F ε g (vectorWord x))

 theorem ActualNormalForm.complex_support {f : Signature AlgebraicComplex n}
    (A : ActualNormalForm f) : exactSupport (fun x => (f (wordVector x):ℂ)) A.shift A.direction := by
  intro x
  rw [←A.support f x]
  constructor
  · intro h hx
    exact h (congrArg (fun z : AlgebraicComplex => (z:ℂ)) hx)
  · intro h hx
    exact h (Subtype.ext hx)

 theorem FlatRadonCards.dimension_cases {r : ℕ} (hr : 1≤r)
    (g : BinaryVector (2*r) → ℂ) (hg : FlatRadonCards g)
    (a : BinaryVector (2*r)) (U : BinaryCode (2*r)) (hs : exactSupport g a U)
    (v : BinaryVector (2*r)) (hv : Accessible v) (hvu : v∉U) :
    ((∀ x,x∈U → dot x v=0) ∧ Module.finrank (ZMod 2) U=r-1) ∨
    (¬(∀ x,x∈U → dot x v=0) ∧ Module.finrank (ZMod 2) U=r) := by
  obtain ⟨F,hF,hflat⟩ := hg v hv
  have H := RadonFrame.nonoverlap_dimension_cases hr F g a U hs (by rwa [hF]) hflat
  simpa only [hF] using H

 theorem FlatRadonCards.not_evenSpace_le_orthogonal {r : ℕ} (hr : 4≤r)
    (g : BinaryVector (2*r) → ℂ) (hg : FlatRadonCards g)
    (a : BinaryVector (2*r)) (U : BinaryCode (2*r)) (hs : exactSupport g a U) :
    ¬evenSpace (2*r)≤dotOrthogonal U := by
  intro hE
  have hu := finrank_le_one_of_evenSpace_le_dotOrthogonal (by omega : 0<2*r) U hE
  have hd := finrank_evenSpace (by omega : 0<2*r)
  obtain ⟨v,hvE,hv,hvu⟩ := exists_accessible_outside_subspace (evenSpace (2*r)) U le_rfl (by omega)
  have hperp : ∀ x,x∈U → dot x v=0 := hE hvE
  rcases FlatRadonCards.dimension_cases (by omega) g hg a U hs v hv hvu with h | h
  · omega
  · exact h.1 hperp

end
end Holant.ReedMuller.AffineRadon
