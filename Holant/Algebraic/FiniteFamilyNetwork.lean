import Holant.Algebraic.FiniteFamilyField
import Holant.Algebraic.NetworkOutputSize
import Holant.NetworkAlgebra

/-! Original finite-family network semantics under the derived common coefficient
field. The basis and its tables are fixed before graph inputs; every original
coefficient and the full assignment sum are retained exactly. -/

namespace Holant.Algebraic

open FixedField

variable {A L : Type*} [Fintype A] [Field L] [Algebra ℚ L] {b : ℕ}

/-- Interpret original literal labels directly in the ambient field. -/
def familyAmbientNetwork (coeff : A → L) (N : FamilyNetwork (A := A) b) : Holant.Network L b where
  shape := N.shape
  vertex v x := coeff (N.vertexLabel v x)
  edge e x y := coeff (N.edgeLabel e x y)

/-- Generated coordinates, using the field proved to contain the whole fixed
family, rather than a supplied coordinate/presentation certificate. -/
noncomputable def commonFieldNetwork (coeff : A → L)
    (halg : ∀ a, IsAlgebraic ℚ (coeff a)) (N : FamilyNetwork (A := A) b) :
    Holant.Network (familyField coeff) b :=
  N.realize (familyPresentation coeff halg) (familyCoordinates coeff halg)

/-- Every original shape, ordered port and coefficient is unchanged. -/
theorem commonFieldNetwork_map (coeff : A → L) (halg : ∀ a, IsAlgebraic ℚ (coeff a))
    (N : FamilyNetwork (A := A) b) :
    (commonFieldNetwork coeff halg N).map (familyField coeff).subtype =
      familyAmbientNetwork coeff N := by
  unfold commonFieldNetwork Holant.Network.map FamilyNetwork.realize familyAmbientNetwork
  congr 1
  · funext v x
    exact familyCoordinates_spec coeff halg (N.vertexLabel v x)
  · funext e x y
    exact familyCoordinates_spec coeff halg (N.edgeLabel e x y)

/-- The exact fixed-field answer is the original ambient-network assignment sum. -/
theorem commonFieldNetwork_denote (coeff : A → L) (halg : ∀ a, IsAlgebraic ℚ (coeff a))
    (N : FamilyNetwork (A := A) b) (x : Fin b → Bool) :
    ((commonFieldNetwork coeff halg N).denote x : L) =
      (familyAmbientNetwork coeff N).denote x := by
  rw [← commonFieldNetwork_map coeff halg N]
  exact (Holant.Network.denote_map (familyField coeff).subtype
    (commonFieldNetwork coeff halg N) x).symm

end Holant.Algebraic
