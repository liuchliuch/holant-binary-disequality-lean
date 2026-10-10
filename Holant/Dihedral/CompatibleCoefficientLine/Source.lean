import Holant.Dihedral.CompatibleCoefficientLine.ActualCards
import Holant.Dihedral.CompatibleCoefficientLine.Minor

/-! Source Lemma 6.5: four fixed actual cards give an analytic factor, or a
compatible nonproportional pair gives an actual quaternary with a literal minor.
Original port permutations and every nonzero representative scalar are explicit. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

/-- Literal physical card on p, in the closure presentation's original port
order. Two native-X wires complement exactly the two binary endpoints. -/
def physicalCard (r : ℕ) (q : Signature Scalar (2*r+4)) (C : Mat) : Signature Scalar (2*r+2) :=
  fun x => ∑ a : Bool, ∑ b : Bool, C (!a) (!b) * q (insertDeleted r a b x)

/-- Source fixed representatives are transported by an actual finite sum.
This normalization is proved and is not an extra caller obligation. -/
theorem physicalCard_normalization {m r : ℕ} {F : SignatureFamily Scalar}
    (G : ActualRepresentatives F m) (q : Signature Scalar (2*r+4))
    (γ : Bool) (t : {t : Scalar // Roots m t}) :
    physicalCard r q (G.binary γ t) = G.multiplier γ t • card r q (M γ t.val) := by
  rw [G.normalization]
  funext x
  simp only [physicalCard,Marked.scale,connection_entry,card,Pi.smul_apply,smul_eq_mul,Fintype.sum_bool]
  ring

/-- The pair's common complementary matching is supplied as ordered source
data, not as a closure or minor certificate. The one permutation fixes the
original port correspondence for both full products. -/
structure CompatibleCards {m r : ℕ} {F : SignatureFamily Scalar}
    (G : ActualRepresentatives F m) (f : Signature Scalar (2*r+4)) where
  order : Equiv.Perm (Fin (2*r+4))
  deleted_first : order ⟨2*r,by omega⟩ = 0
  deleted_second : order ⟨2*r+1,by omega⟩ = 1
  protected_first : order ⟨2*r+2,by omega⟩ = 2
  protected_second : order ⟨2*r+3,by omega⟩ = 3
  sector : Bool → Bool
  phase : Bool → {t : Scalar // Roots m t}
  actualScalar : Bool → Scalar
  actualScalar_ne_zero : ∀ b, actualScalar b ≠ 0
  originalScalar : Bool → Scalar
  originalScalar_ne_zero : ∀ b, originalScalar b ≠ 0
  complement : Bool → Fin r → Mat
  edgeFactor : Bool → Mat
  parity : Fin r → Bool
  complement_parity : ∀ b e, HasParity (parity e) (complement b e)
  protectedParity : Bool
  protected_parity : ∀ b, HasParity protectedParity (edgeFactor b)
  actual : ∀ b, Gadget.Realizes F .disequality
    (actualScalar b • physicalCard r (Tensor.reindex order.symm f) (G.binary (sector b) (phase b)))
  equation : ∀ b, actualScalar b • physicalCard r (Tensor.reindex order.symm f)
    (G.binary (sector b) (phase b)) = originalScalar b • product r (complement b) (edgeFactor b)

/-- Remove only recorded nonzero physical multipliers. -/
theorem CompatibleCards.normalized {m r : ℕ} {F : SignatureFamily Scalar}
    {G : ActualRepresentatives F m} {f : Signature Scalar (2*r+4)}
    (D : CompatibleCards G f) (b : Bool) :
    card r (Tensor.reindex D.order.symm f) (M (D.sector b) (D.phase b).val) =
      (D.originalScalar b / (D.actualScalar b*G.multiplier (D.sector b) (D.phase b))) •
        product r (D.complement b) (D.edgeFactor b) := by
  have hh := D.equation b
  rw [physicalCard_normalization,smul_smul] at hh
  funext x
  have he := congrFun hh x
  simp only [Pi.smul_apply,smul_eq_mul] at he ⊢
  have hd := mul_ne_zero (D.actualScalar_ne_zero b) (G.multiplier_ne_zero (D.sector b) (D.phase b))
  field_simp [D.actualScalar_ne_zero b,G.multiplier_ne_zero (D.sector b) (D.phase b)]
  linear_combination he

/-- The source conditional branch, including the fixed actual group binaries.
There is one original ancestor and one shared residual ordering. No hypothesis
or conclusion permits simultaneous traces across different parity patterns. -/
theorem source_coefficient_quaternary {m r : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (f : Signature Scalar (2*r+4)) (hf : Gadget.Realizes F .disequality f)
    (D : CompatibleCards (G.connections (by omega)) f)
    (hline : ¬ ProjectivelyEqual (D.edgeFactor true) (D.edgeFactor false)) :
    ∃ Q : Signature Scalar 4, Gadget.Realizes F .disequality Q ∧
      TraceSequence (G.connections (by omega)) r (Tensor.reindex D.order.symm f) Q ∧
      ∃ p₀ p₁ : Bool × Bool, minor Q p₀ p₁ (false,D.protectedParity) (true,!D.protectedParity) ≠ 0 := by
  let C := G.connections (by omega : 0<m)
  have hz (b : Bool) : D.originalScalar b / (D.actualScalar b*C.multiplier (D.sector b) (D.phase b)) ≠ 0 :=
    div_ne_zero (D.originalScalar_ne_zero b)
      (mul_ne_zero (D.actualScalar_ne_zero b) (C.multiplier_ne_zero (D.sector b) (D.phase b)))
  exact source_compatible_quaternary hm F C _ (realizes_reindex F .disequality f hf D.order)
    _ _ _ _ _ _ D.parity (D.complement_parity false) (D.complement_parity true)
    D.protectedParity (D.protected_parity false) (D.protected_parity true) hline
    _ _ (hz false) (hz true) (D.normalized false) (D.normalized true)

/-- Four common-parity factors either have the exact source analytic tensor
factor, or supply a genuine nonproportional pair. The physical closure of that
pair is conditional on CompatibleCards, precisely as in the manuscript. -/
theorem source_coefficient_line_or_pair {n r : ℕ} {F : SignatureFamily Scalar}
    {t₀ t₁ : Scalar} {f : Signature Scalar (n+4)}
    (D : FourProducts (r:=r) F t₀ t₁ f) (ht : t₀ ≠ t₁)
    (α : Bool) (hparity : ∀ i, HasParity α (D.factors i (D.edge i))) :
    (∃ h : Signature Scalar (n+2), IsMonomial (D.factors (false,false) (D.edge (false,false))) ∧
      ∀ a b c d x, f (pair a b (pair c d x)) =
        D.factors (false,false) (D.edge (false,false)) c d * h (pair a b x)) ∨
    (∃ i j : Sample, ¬ ProjectivelyEqual (D.factors j (D.edge j)) (D.factors i (D.edge i)) ∧
      factorDet α (D.factors i (D.edge i)) (D.factors j (D.edge j)) ≠ 0) := by
  classical
  by_cases h : ∀ i, ProjectivelyEqual (D.factors i (D.edge i)) (D.factors (false,false) (D.edge (false,false)))
  · left
    obtain ⟨w,hw,he⟩ := hparity (false,false)
    exact source_genuine_factor D ht _ ⟨α,w,hw,he⟩ h
  · right
    push_neg at h
    obtain ⟨j,hj⟩ := h
    exact ⟨(false,false),j,hj,fun hh => hj ((factorDet_zero_iff (hparity _) (hparity _)).mp hh)⟩

/-- Complete source dichotomy. In the second alternative a chosen pair has a
nonzero literal coefficient determinant; every shared complementary matching
presentation with the source parity compatibility gives the physical minor.
The alignment conditions retain the same two selected original sampled cards. -/
theorem source_coefficient_line_quaternary_or_factor {m r k : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily Scalar) (G : TransferRepresentatives F m)
    (t : Bool → {t : Scalar // Roots m t}) (ht : (t false).val ≠ (t true).val)
    (f : Signature Scalar (2*r+4)) (hf : Gadget.Realizes F .disequality f)
    (D : PhysicalFourProducts (r:=k) (G.connections (by omega)) t f)
    (β : Bool) (hparity : ∀ i, HasParity β (D.factors i (D.edge i))) :
    (∃ h : Signature Scalar (2*r+2), IsMonomial (D.factors (false,false) (D.edge (false,false))) ∧
      f = Tensor.reindex (factorPorts (2*r))
        (Tensor.tensor (Tractable.kernelSignature (D.factors (false,false) (D.edge (false,false)))) h)) ∨
    (∃ j : Sample, factorDet β (D.factors (false,false) (D.edge (false,false))) (D.factors j (D.edge j)) ≠ 0 ∧
      ∀ C : CompatibleCards (G.connections (by omega)) f,
        C.sector false = false → C.phase false = t false →
        C.sector true = j.1 → C.phase true = t j.2 →
        C.edgeFactor false = D.factors (false,false) (D.edge (false,false)) →
        C.edgeFactor true = D.factors j (D.edge j) →
        ∃ Q : Signature Scalar 4, Gadget.Realizes F .disequality Q ∧
          TraceSequence (G.connections (by omega)) r (Tensor.reindex C.order.symm f) Q ∧
          ∃ p₀ p₁ : Bool × Bool,
            minor Q p₀ p₁ (false,C.protectedParity) (true,!C.protectedParity) ≠ 0) := by
  classical
  by_cases h : ∀ i, ProjectivelyEqual (D.factors i (D.edge i)) (D.factors (false,false) (D.edge (false,false)))
  · left
    obtain ⟨w,hw,he⟩ := hparity (false,false)
    exact source_physical_genuine_factor (by omega) F G t ht f D _ ⟨β,w,hw,he⟩ h
  · right
    push_neg at h
    obtain ⟨j,hj⟩ := h
    refine ⟨j,fun hh => hj ((factorDet_zero_iff (hparity _) (hparity _)).mp hh),?_⟩
    intro C _ _ _ _ he₀ he₁
    apply source_coefficient_quaternary hm F G f hf C
    simpa only [he₀,he₁] using hj

/-- Different parity patterns cannot be silently fed to the simultaneous
trace rule: every monomial closure kills at least one of these two factors. -/
theorem incompatible_parities_no_common_trace (a b t : Scalar) (γ : Bool) :
    trace (M false a) (M γ t)=0 ∨ trace (M true b) (M γ t)=0 := by
  cases γ
  · right; simp [trace,M,monomial]
  · left; simp [trace,M,monomial]

end Holant.Dihedral.CompatibleCoefficientLine
