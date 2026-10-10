import Holant.OpenNetworkComposition.ProjectiveContractionWire

/-! Exact semantic obstruction from a free/free native-X edge. Its complete
binary factor and the full remaining tensor are retained, without cancelling
or discarding any scalar component. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.FactorFreeNormalization
variable {K : Type*} {n : ℕ}

abbrev OtherPorts (i j : Fin n) := {k : Fin n // k≠i ∧ k≠j}

/-- An isolated binary X factor at two distinct original ordered coordinates. -/
def HasXFactor [CommSemiring K] (h : Signature K n) : Prop :=
  ∃i j : Fin n,i≠j ∧ ∃g : Tensor K (OtherPorts i j),
    ∀x,h x=Signature.disequality (x i) (x j)*g (fun k => x k.val)

/-- A semantic condition sufficient to eliminate all free stubs with no new
vertices or additional signature-family membership assumption. -/
def NoXFactor [CommSemiring K] (h : Signature K n) : Prop := ¬HasXFactor h

/-- Enumerate exactly the original boundary positions outside the chosen pair. -/
def remaining (i j : Fin n) : Fin (Fintype.card (OtherPorts i j)) ↪ Fin n where
  toFun k := ((Fintype.equivFin (OtherPorts i j)).symm k).val
  inj' := by
    intro a b hab
    exact (Fintype.equivFin (OtherPorts i j)).symm.injective (Subtype.ext hab)

theorem remaining_range (i j k : Fin n) :
    (∃l,remaining i j l=k) ↔ k≠i ∧ k≠j := by
  constructor
  · rintro ⟨l,rfl⟩
    exact ((Fintype.equivFin (OtherPorts i j)).symm l).property
  · intro hk
    refine ⟨Fintype.equivFin (OtherPorts i j) ⟨k,hk⟩,?_⟩
    simp [remaining]

variable [CommSemiring K]

/-- The repository's actual corrected tensor has an exact X factor whenever
one edge pairs two free stubs. All other vertices and scalar factors survive. -/
theorem hasXFactor_of_free_mate {V F E : Type*}
    [Fintype V] [Fintype F] [Fintype E]
    (M : FiniteNetwork K V F E n) (he : ∀e,M.edge e=.disequality)
    (f g : F)
    (hop : M.shape.ends ((M.shape.freeEdge f).1,!(M.shape.freeEdge f).2)=.inr g) :
    HasXFactor M.tensor := by
  let i := M.shape.freeBoundary f
  let j := M.shape.freeBoundary g
  have hfg := ProjectiveContraction.Wire.free_ne M.shape f g hop
  have hij : i≠j := by
    intro hij
    have h := congrArg M.shape.boundary hij
    change M.shape.boundary (M.shape.freeBoundary f)=M.shape.boundary (M.shape.freeBoundary g) at h
    rw [M.shape.free_boundary,M.shape.free_boundary] at h
    exact hfg (Sum.inr.inj h)
  let R := ProjectiveContraction.Wire.network M f g hop i j
    (M.shape.free_boundary f) (M.shape.free_boundary g) (remaining i j) (remaining_range i j)
  refine ⟨i,j,hij,fun x => R.tensor (fun k => x ((Fintype.equivFin (OtherPorts i j)).symm k)),?_⟩
  intro x
  exact ProjectiveContraction.Wire.tensor_factor M f g hop i j
    (M.shape.free_boundary f) (M.shape.free_boundary g) (remaining i j) (remaining_range i j) he x

end Holant.OpenNetworkComposition.FactorFreeNormalization
