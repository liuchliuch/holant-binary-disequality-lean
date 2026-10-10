import Holant.Proofs.Closure.HistorySectorCards

/-! The SAME ordered CURRENT matching presentation transports to weighted
sector coordinates. Its original-L scalar, edge indexing and port bijection
are preserved. Validity uses the actual transformed transfer and sector edge. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCards
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
variable {L : Type*} [Field L] {n : ℕ}

def matching (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (M : Presentation L (Fin n)) : Presentation AlgebraicComplex (Fin n) where
  edges := M.edges
  ports := M.ports
  matrix e := Matrix.of (transport U (mapBinary phi (M.matrix e)))
  scalar := phi M.scalar

@[simp] theorem matching_ports (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (M : Presentation L (Fin n)) : (matching phi U M).ports = M.ports := rfl

@[simp] theorem matching_scalar (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (M : Presentation L (Fin n)) : (matching phi U M).scalar = phi M.scalar := rfl

/-- Finite Fubini at the recorded original perfect matching, with no change
of scalar or port partition and no chosen replacement presentation. -/
theorem matching_tensor (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (M : Presentation L (Fin n)) :
    U.symm.action (RH.mapSignature phi M.tensor) = (matching phi U M).tensor := by
  classical
  funext x
  change (∑ y : Fin n → Bool, (∏ j, U.inverse (x j) (y j)) *
      phi (M.scalar * ∏ e, M.matrix e (y (M.ports (e,false))) (y (M.ports (e,true))))) =
    phi M.scalar * ∏ e, transport U (mapBinary phi (M.matrix e))
      (x (M.ports (e,false))) (x (M.ports (e,true)))
  simp only [_root_.map_mul,_root_.map_prod]
  change (∑ y : Fin n → Bool, (∏ j, U.inverse (x j) (y j)) *
      (phi M.scalar * ∏ e, mapBinary phi (M.matrix e) (y (M.ports (e,false))) (y (M.ports (e,true))))) = _
  let assignments : (Fin n → Bool) ≃ ((Fin M.edges × Bool) → Bool) :=
    Equiv.arrowCongr M.ports.symm (Equiv.refl Bool)
  have hs : (∑ y : Fin n → Bool, (∏ j, U.inverse (x j) (y j)) *
      (phi M.scalar * ∏ e, mapBinary phi (M.matrix e) (y (M.ports (e,false))) (y (M.ports (e,true))))) =
      phi M.scalar * ∑ z : (Fin M.edges × Bool) → Bool, ∏ e,
        U.inverse (x (M.ports (e,false))) (z (e,false)) *
        U.inverse (x (M.ports (e,true))) (z (e,true)) *
        mapBinary phi (M.matrix e) (z (e,false)) (z (e,true)) := by
    rw [Finset.mul_sum]
    apply Fintype.sum_equiv assignments
    intro y
    rw [←M.ports.prod_comp (fun j => U.inverse (x j) (y j)),Fintype.prod_prod_type]
    simp only [Fintype.prod_bool]
    change _ = phi M.scalar * ∏ e,
      U.inverse (x (M.ports (e,false))) (y (M.ports (e,false))) *
      U.inverse (x (M.ports (e,true))) (y (M.ports (e,true))) *
      mapBinary phi (M.matrix e) (y (M.ports (e,false))) (y (M.ports (e,true)))
    rw [mul_left_comm _ (phi M.scalar),←Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro e _
    ring
  rw [hs,Network.sum_halfEdge_products M.edges (fun e a b =>
    U.inverse (x (M.ports (e,false))) a * U.inverse (x (M.ports (e,true))) b *
      mapBinary phi (M.matrix e) a b)]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  simp only [transport,mapBinary,Kernel.mul,Kernel.transpose,Fintype.sum_bool]
  ring

def sectorTransfers (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) : Set Mat :=
  {T | ∃ C ∈ actualTransfers F, T = conjugate U.symm (mapBinary phi C)}

/-- The changed binary table is valid through multiplication by the ACTUAL
sector edge. The semantic transfer is the original actual BX conjugated. -/
theorem matching_valid (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (M : Presentation L (Fin n)) (valid : M.Valid (actualTransfers F))
    (e : Fin M.edges) :
    Kernel.mul ((matching phi U M).matrix e) (sectorEdge U) ∈ sectorTransfers phi U F := by
  refine ⟨transfer (M.matrix e),valid e,?_⟩
  change Kernel.mul (transport U (mapBinary phi (M.matrix e))) (sectorEdge U) = _
  rw [transport_mul_edge]
  unfold sectorTransfer
  rw [transfer,map_mul,map_X]

/-- A sector matching carries its literal ORIGINAL-field presentation as its
witness. Thus repeated binary factors and all ordered ports remain visible. -/
def MatchingInSector (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (g : Signature AlgebraicComplex n) : Prop :=
  g = 0 ∨ ∃ M : Presentation L (Fin n), M.Valid (actualTransfers F) ∧ M.scalar ≠ 0 ∧
    g = (matching phi U M).tensor

theorem matching_transport (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (g : Signature L n)
    (stable : MatchingOrZero (actualTransfers F) g) :
    MatchingInSector phi U F (U.symm.action (RH.mapSignature phi g)) := by
  rcases stable with hz | ⟨M,valid,scalar,rfl⟩
  · left
    rw [hz]
    have he : RH.mapSignature phi (0 : Signature L n) = 0 := by funext x; exact phi.map_zero
    rw [he,ClosureFactorTreeAction.action_zero]
  · exact Or.inr ⟨M,valid,scalar,matching_tensor phi U M⟩

/-- Stable CURRENT raw cards become matching products at the SAME marked
basis and actual changed edge. The zero alternative is retained. -/
theorem current_card_matching {m : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g)
    (key : RawCardKey m (completeGroup F torsion)) :
    MatchingInSector phi U F (card phi U F torsion f key) := by
  rw [←card_transport]
  exact matching_transport phi U F _ (stable _ (Or.inr ⟨key,rfl⟩))

theorem matching_scalar_nonzero (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (M : Presentation L (Fin n)) (nonzero : M.scalar ≠ 0) :
    (matching phi U M).scalar ≠ 0 := (map_ne_zero phi).mpr nonzero

theorem current_deck_matching {m : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2))
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g) :
    ∀ g ∈ deck phi U F torsion f, MatchingInSector phi U F g := by
  intro g hg
  rw [deck_exact] at hg
  obtain ⟨h,hh,rfl⟩ := hg
  exact matching_transport phi U F h (stable h hh)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCards
end
