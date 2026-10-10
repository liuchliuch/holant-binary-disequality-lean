import Holant.Dihedral.CompatibleCoefficientLine.MatchingAlignment

/-! Construct the physical compatible presentation directly from any two of
the original four cards and their literal common complementary matching. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

theorem edgeOrder_other {r : ℕ} (e : Fin (r+1)) (d : Fin r) : edgeOrder e d.castSucc ≠ e := by
  intro h
  have hh : edgeOrder e d.castSucc = edgeOrder e (Fin.last r) := by simpa [edgeOrder] using h
  have hv := congrArg Fin.val ((edgeOrder e).injective hh)
  simp only [Fin.val_castSucc,Fin.val_last] at hv
  omega

theorem ordered_physical_smul (r : ℕ) (p : Equiv.Perm (Fin (2*r+2)))
    (f : Signature Scalar (2*r+4)) (C : Mat) (c : Scalar) :
    c • physicalCard r (Tensor.reindex (ancestorOrder r p).symm f) C =
      Tensor.reindex p.symm (c • nativeCardValue f C) := by
  rw [ordered_physicalCard]
  rfl

/-- The literal source common matching and parity condition is the only extra
input. Actuality, physical normalization, both full product equations, the
protected original ports, and the shared permutation are all constructed. -/
def PhysicalFourProducts.compatibleCards {m r : ℕ} {F : SignatureFamily Scalar}
    {G : ActualRepresentatives F m} {t : Bool → {t : Scalar // Roots m t}}
    {f : Signature Scalar (2*r+4)} (D : PhysicalFourProducts (r:=r+1) G t f)
    (i j : Sample) (L : MatchingAlignment (D.ports i) (D.ports j))
    (β : Bool) (hB₀ : HasParity β (D.factors i (D.edge i)))
    (hB₁ : HasParity β (D.factors j (D.edge j)))
    (hcompat : ∀ e, e ≠ D.edge i → ∃ α : Bool,
      HasParity α (D.factors i e) ∧ HasParity α (L.factors (D.factors j) e)) :
    CompatibleCards G f := by
  let p := matchingOrder (D.ports i) (D.edge i)
  have hprotected := L.protected_edge (D.edge i) (D.edge j) (D.first i) (D.first j)
  have hedge : L.factors (D.factors j) (D.edge i) = D.factors j (D.edge j) := by
    simp [MatchingAlignment.factors,hprotected.1,hprotected.2]
  choose α hα₀ hα₁ using fun e : Fin r => hcompat (edgeOrder (D.edge i) e.castSucc) (edgeOrder_other _ _)
  refine {
    order := ancestorOrder r p
    deleted_first := ?_
    deleted_second := ?_
    protected_first := ?_
    protected_second := ?_
    sector := fun b => (if b then j else i).1
    phase := fun b => t (if b then j else i).2
    actualScalar := fun b => D.actualScalar (if b then j else i)
    actualScalar_ne_zero := fun b => D.actualScalar_ne_zero _
    originalScalar := fun b => D.originalScalar (if b then j else i)
    originalScalar_ne_zero := fun b => D.originalScalar_ne_zero _
    complement := fun b e => if b then L.factors (D.factors j) (edgeOrder (D.edge i) e.castSucc)
      else D.factors i (edgeOrder (D.edge i) e.castSucc)
    edgeFactor := fun b => if b then D.factors j (D.edge j) else D.factors i (D.edge i)
    parity := α
    complement_parity := ?_
    protectedParity := β
    protected_parity := ?_
    actual := ?_
    equation := ?_ }
  · change liftPair p (shuffleDeleted r ⟨2*r,by omega⟩)=0
    rw [shuffleDeleted_p0]
    rfl
  · change liftPair p (shuffleDeleted r ⟨2*r+1,by omega⟩)=1
    rw [shuffleDeleted_p1]
    rfl
  · change liftPair p (shuffleDeleted r ⟨2*r+2,by omega⟩)=2
    rw [shuffleDeleted_e0]
    have he : (⟨2*r,by omega⟩ : Fin (2*r+2)) = pairPorts r (Fin.last r,false) := by
      apply Fin.ext; simp [pairPorts_val]
    change (p ⟨2*r,by omega⟩).succ.succ = 2
    rw [he,matchingOrder_pair]
    simp [edgeOrder,D.first]
  · change liftPair p (shuffleDeleted r ⟨2*r+3,by omega⟩)=3
    rw [shuffleDeleted_e1]
    have he : (⟨2*r+1,by omega⟩ : Fin (2*r+2)) = pairPorts r (Fin.last r,true) := by
      apply Fin.ext; simp [pairPorts_val]
    change (p ⟨2*r+1,by omega⟩).succ.succ = 3
    rw [he,matchingOrder_pair]
    simp [edgeOrder,D.second]
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2<2*r+2+1),Nat.mod_eq_of_lt (by omega : 3<2*r+2+1+1)]
  · intro b e
    cases b
    · exact hα₀ e
    · exact hα₁ e
  · intro b
    cases b
    · exact hB₀
    · exact hB₁
  · intro b
    rw [ordered_physical_smul]
    exact realizes_reindex F .disequality _ (D.actual _) p
  · intro b
    rw [ordered_physical_smul,D.equation]
    cases b
    · exact reindex_matching_product _ _ _ _
    · simp only [ite_true]
      rw [← L.product_eq (D.factors j),reindex_matching_product,hedge]

/-- Full source nonproportional branch for ANY selected pair of the four actual
cards. Only their literal common matching and complementary parity agreement
are supplied; the entire physical compatible presentation is derived. -/
theorem source_selected_coefficient_quaternary {m r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (t : Bool → {t : Scalar // Roots m t})
    (f : Signature Scalar (2*r+4)) (hf : Gadget.Realizes F .disequality f)
    (D : PhysicalFourProducts (r:=r+1) (G.connections (by omega)) t f)
    (i j : Sample) (L : MatchingAlignment (D.ports i) (D.ports j))
    (β : Bool) (hB₀ : HasParity β (D.factors i (D.edge i)))
    (hB₁ : HasParity β (D.factors j (D.edge j)))
    (hline : ¬ ProjectivelyEqual (D.factors j (D.edge j)) (D.factors i (D.edge i)))
    (hcompat : ∀ e, e ≠ D.edge i → ∃ α : Bool,
      HasParity α (D.factors i e) ∧ HasParity α (L.factors (D.factors j) e)) :
    ∃ Q : Signature Scalar 4, Gadget.Realizes F .disequality Q ∧
      TraceSequence (G.connections (by omega)) r
        (Tensor.reindex (ancestorOrder r (matchingOrder (D.ports i) (D.edge i))).symm f) Q ∧
      ∃ p₀ p₁ : Bool × Bool, minor Q p₀ p₁ (false,β) (true,!β) ≠ 0 := by
  exact source_coefficient_quaternary hm F G f hf (D.compatibleCards i j L β hB₀ hB₁ hcompat) hline

end Holant.Dihedral.CompatibleCoefficientLine
