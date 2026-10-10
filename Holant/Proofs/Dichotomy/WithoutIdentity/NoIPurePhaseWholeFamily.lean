import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseWholeFamilyGraph
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareDataCore

/-! The genuinely sourced nonzero-row tensor at the unchanged target.
The graph theorem chooses one phase before all original rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamily
open Holant Holant.Tractable Holant.Algebraic
namespace G
export NoIPurePhaseWholeFamilyGraph (row bundle value indices whole wholeValue)
end G
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'

abbrev row:=G.row D.K D.table
abbrev bundle:=G.bundle D.K D.table
abbrev value:=G.value D.K D.table
abbrev indices:=G.indices D.K D.table
abbrev whole:=G.whole D.K D.table
abbrev wholeValue:=G.wholeValue D.K D.table

theorem whole_nonzero : wholeValue target D≠0 :=
  NoIPurePhaseWholeFamilyGraph.whole_nonzero D.K D.table

theorem all_rows (C : EOClass) (r : AlgebraicComplex) (hr : r≠0)
    (good : C.Holds (twist r (wholeValue target D))) :
    ∀j,C.Holds (twist r (row target D j)) :=
  NoIPurePhaseWholeFamilyGraph.all_rows D.K D.table C r hr good

theorem common_chart {α : Type} (phase : α→AlgebraicComplex) (nonzero : ∀i,phase i≠0)
    (good : ∃i,Affine (twist (phase i) (wholeValue target D))) :
    ∃i,∀j,Affine (twist (phase i) (row target D j)) :=
  NoIPurePhaseWholeFamilyGraph.common_chart D.K D.table phase nonzero good

theorem common_product_chart {α : Type} (phase : α→AlgebraicComplex) (nonzero : ∀i,phase i≠0)
    (good : ∃i,Product (twist (phase i) (wholeValue target D))) :
    ∃i,∀j,Product (twist (phase i) (row target D j)) :=
  NoIPurePhaseWholeFamilyGraph.common_product_chart D.K D.table phase nonzero good


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamily
end
