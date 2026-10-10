import Holant.Dihedral.CompatibleCoefficientLine.AlignedSource
import Holant.Dihedral.CompatibleCoefficientLine.MatchingAgreement

/-! Full source Lemma 6.5. Compatibility is now the literal original partner
function and support-parity agreement, not a supplied physical presentation. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.EndpointParallelogram

theorem HasParity.transpose {α : Bool} {A : Mat} (h : HasParity α A) : HasParity α (Kernel.transpose A) := by
  obtain ⟨w,hw,rfl⟩ := h
  exact ⟨fun a => w (a ^^ α),fun a => hw _,monomial_transpose α w⟩

def CommonComplement {m r : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
    {t : Bool → {t : Scalar // Roots m t}} {f : Signature Scalar (2*r+4)}
    (D : PhysicalFourProducts (r:=r+1) G t f) (i j : Sample) : Prop :=
  ∀ u : Fin (2*r+2), u ≠ 0 → u ≠ 1 →
    (Pairing.ofPorts (D.ports i)).mate u = (Pairing.ofPorts (D.ports j)).mate u

/-- Common support parity of the other original edges, using their actual
opposite-card edge IDs found from the original endpoint, before any reordering. -/
def CommonParity {m r : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
    {t : Bool → {t : Scalar // Roots m t}} {f : Signature Scalar (2*r+4)}
    (D : PhysicalFourProducts (r:=r+1) G t f) (i j : Sample) : Prop :=
  ∀ e, e ≠ D.edge i → ∃ α : Bool, HasParity α (D.factors i e) ∧
    HasParity α (D.factors j (((D.ports j).symm (D.ports i (e,false))).1))

theorem commonComplement_all {m r : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
    {t : Bool → {t : Scalar // Roots m t}} {f : Signature Scalar (2*r+4)}
    (D : PhysicalFourProducts (r:=r+1) G t f) (i j : Sample) (h : CommonComplement D i j) :
    ∀ u, (Pairing.ofPorts (D.ports i)).mate u = (Pairing.ofPorts (D.ports j)).mate u := by
  have hzero (k : Sample) : (Pairing.ofPorts (D.ports k)).mate 0 = 1 := by
    rw [← D.first k]
    simp only [Pairing.ofPorts,Equiv.symm_apply_apply,Bool.not_false]
    exact D.second k
  have hone (k : Sample) : (Pairing.ofPorts (D.ports k)).mate 1 = 0 := by
    rw [← D.second k]
    simp only [Pairing.ofPorts,Equiv.symm_apply_apply,Bool.not_true]
    exact D.first k
  intro u
  by_cases h₀ : u=0
  · subst u; rw [hzero,hzero]
  by_cases h₁ : u=1
  · subst u; rw [hone,hone]
  exact h u h₀ h₁

/-- Source nonproportional branch for arbitrary selected actual cards. The
common matching/parity hypotheses directly construct the closure and minor. -/
theorem source_any_compatible_pair {m r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (t : Bool → {t : Scalar // Roots m t})
    (f : Signature Scalar (2*r+4)) (hf : Gadget.Realizes F .disequality f)
    (D : PhysicalFourProducts (r:=r+1) (G.connections (by omega)) t f)
    (i j : Sample) (β : Bool) (hB₀ : HasParity β (D.factors i (D.edge i)))
    (hB₁ : HasParity β (D.factors j (D.edge j)))
    (hline : ¬ ProjectivelyEqual (D.factors j (D.edge j)) (D.factors i (D.edge i)))
    (hmatching : CommonComplement D i j) (hparity : CommonParity D i j) :
    ∃ Q : Signature Scalar 4, Gadget.Realizes F .disequality Q ∧
      TraceSequence (G.connections (by omega)) r
        (Tensor.reindex (ancestorOrder r (matchingOrder (D.ports i) (D.edge i))).symm f) Q ∧
      ∃ p₀ p₁ : Bool × Bool, minor Q p₀ p₁ (false,β) (true,!β) ≠ 0 := by
  let L := MatchingAlignment.ofMate (D.ports i) (D.ports j) (commonComplement_all D i j hmatching)
  apply source_selected_coefficient_quaternary hm F G t f hf D i j L β hB₀ hB₁ hline
  intro e he
  obtain ⟨α,ha,hb⟩ := hparity e he
  refine ⟨α,ha,?_⟩
  change HasParity α (if L.flip e then Kernel.transpose (D.factors j (L.edge e)) else D.factors j (L.edge e))
  have hh : HasParity α (D.factors j (L.edge e)) := hb
  cases hflip : L.flip e
  · exact hh
  · exact hh.transpose

/-- Lemma 6.5, with literal actual-card normalization, exact analytic tensor
factorization, and the conditional physical conclusion for EVERY nonproportional
selected pair. No realization premise is imposed on B_e or the complementary h. -/
theorem source_coefficient_line {m r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (t : Bool → {t : Scalar // Roots m t}) (ht : (t false).val ≠ (t true).val)
    (f : Signature Scalar (2*r+4)) (hf : Gadget.Realizes F .disequality f)
    (D : PhysicalFourProducts (r:=r+1) (G.connections (by omega)) t f)
    (β : Bool) (hparity : ∀ i, HasParity β (D.factors i (D.edge i))) :
    (∃ h : Signature Scalar (2*r+2), IsMonomial (D.factors (false,false) (D.edge (false,false))) ∧
      f = Tensor.reindex (factorPorts (2*r))
        (Tensor.tensor (Tractable.kernelSignature (D.factors (false,false) (D.edge (false,false)))) h)) ∨
    ((∃ i j : Sample, factorDet β (D.factors i (D.edge i)) (D.factors j (D.edge j)) ≠ 0) ∧
      ∀ i j : Sample,
        ¬ ProjectivelyEqual (D.factors j (D.edge j)) (D.factors i (D.edge i)) →
        CommonComplement D i j → CommonParity D i j →
        ∃ Q : Signature Scalar 4, Gadget.Realizes F .disequality Q ∧
          TraceSequence (G.connections (by omega)) r
            (Tensor.reindex (ancestorOrder r (matchingOrder (D.ports i) (D.edge i))).symm f) Q ∧
          ∃ p₀ p₁ : Bool × Bool, minor Q p₀ p₁ (false,β) (true,!β) ≠ 0) := by
  classical
  by_cases h : ∀ i, ProjectivelyEqual (D.factors i (D.edge i)) (D.factors (false,false) (D.edge (false,false)))
  · left
    obtain ⟨w,hw,he⟩ := hparity (false,false)
    exact source_physical_genuine_factor (by omega) F G t ht f D _ ⟨β,w,hw,he⟩ h
  · right
    push_neg at h
    obtain ⟨j,hj⟩ := h
    refine ⟨⟨(false,false),j,fun hh => hj ((factorDet_zero_iff (hparity _) (hparity _)).mp hh)⟩,?_⟩
    intro i j hij hmatching hcompatible
    exact source_any_compatible_pair hm F G t f hf D i j β (hparity i) (hparity j) hij hmatching hcompatible

end Holant.Dihedral.CompatibleCoefficientLine
