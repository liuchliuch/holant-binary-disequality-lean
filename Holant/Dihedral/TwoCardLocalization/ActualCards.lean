import Holant.Dihedral.TwoCardLocalization.ThreeFactor

/-! Source input consists of the selected two actual cards of one original
ancestor, with fixed representatives, exact scalars and original matching data. -/
noncomputable section
namespace Holant.Dihedral.TwoCardLocalization
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
open Holant.Dihedral.EndpointParallelogram Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false

structure PairProducts {m r : ℕ} {F : SignatureFamily Scalar} (G : ActualRepresentatives F m)
    (labels : Bool → PhaseLabel m) (f : Signature Scalar (2*r+6)) where
  ports : Bool → (Fin (r+2) × Bool) ≃ Fin (2*r+4)
  factors : Bool → Fin (r+2) → Mat
  factors_mem : ∀ b e,factors b e ∈ groupM m
  scalar : Bool → Scalar
  scalar_ne_zero : ∀ b,scalar b ≠ 0
  actualScalar : Bool → Scalar
  actualScalar_ne_zero : ∀ b,actualScalar b ≠ 0
  actual : ∀ b,Gadget.Realizes F .disequality
    (actualScalar b • nativeCardValue f (G.binary (labels b).1 (labels b).2))
  equation : ∀ b,actualScalar b • nativeCardValue f (G.binary (labels b).1 (labels b).2)=
    MatchingContractionClosure.productValue (ports b) (factors b) (scalar b)

def relativeFactor {r n : ℕ} (p₀ p₁ : (Fin r × Bool) ≃ Fin n) (A : Fin r → Mat) (e : Fin r) : Mat :=
  let x := p₁.symm (p₀ (e,false))
  if x.2 then Kernel.transpose (A x.1) else A x.1

/-- Exact source disagreement, read from original physical ports and factor
entries. No residual presentation, closure program or obstruction is supplied. -/
def PairProducts.Disagrees {m r : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
    {labels : Bool → PhaseLabel m} {f : Signature Scalar (2*r+6)} (D : PairProducts G labels f) : Prop :=
  (Pairing.ofPorts (D.ports false)).mate ≠ (Pairing.ofPorts (D.ports true)).mate ∨
  ((Pairing.ofPorts (D.ports false)).mate = (Pairing.ofPorts (D.ports true)).mate ∧
    ∃ e g : Fin (r+2),e ≠ g ∧
      ¬ ProjectivelyEqual (relativeFactor (D.ports false) (D.ports true) (D.factors true) e) (D.factors false e) ∧
      ¬ ProjectivelyEqual (relativeFactor (D.ports false) (D.ports true) (D.factors true) g) (D.factors false g))

def PairProducts.normalizedScalar {m r : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
    {labels : Bool → PhaseLabel m} {f : Signature Scalar (2*r+6)} (D : PairProducts G labels f) (b : Bool) : Scalar :=
  D.scalar b / (D.actualScalar b*G.multiplier (labels b).1 (labels b).2)

theorem PairProducts.normalizedScalar_ne_zero {m r : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
    {labels : Bool → PhaseLabel m} {f : Signature Scalar (2*r+6)} (D : PairProducts G labels f) (b : Bool) :
    D.normalizedScalar b ≠ 0 :=
  div_ne_zero (D.scalar_ne_zero b)
    (mul_ne_zero (D.actualScalar_ne_zero b) (G.multiplier_ne_zero _ _))

/-- Normalize by the actual fixed representative scalars via the proved
native-X finite sum; this is not a caller-supplied normalization identity. -/
theorem PairProducts.normalized {m r : ℕ} {F : SignatureFamily Scalar} {G : ActualRepresentatives F m}
    {labels : Bool → PhaseLabel m} {f : Signature Scalar (2*r+6)} (D : PairProducts G labels f) (b : Bool) :
    Signature.contract (TwoCardLocalization.phaseKernel (labels b)) f=
      MatchingContractionClosure.productValue (D.ports b) (D.factors b) (D.normalizedScalar b) := by
  have hh := D.equation b
  rw [G.normalization,actual_close,smul_smul] at hh
  funext x
  have he := congrFun hh x
  change (D.actualScalar b*G.multiplier (labels b).1 (labels b).2)*
    Signature.contract (TwoCardLocalization.phaseKernel (labels b)) f x =
      D.scalar b*∏ e,D.factors b e (x (D.ports b (e,false))) (x (D.ports b (e,true))) at he
  change Signature.contract (TwoCardLocalization.phaseKernel (labels b)) f x =
    (D.scalar b/(D.actualScalar b*G.multiplier (labels b).1 (labels b).2))*
      ∏ e,D.factors b e (x (D.ports b (e,false))) (x (D.ports b (e,true)))
  field_simp [D.actualScalar_ne_zero b,G.multiplier_ne_zero (labels b).1 (labels b).2]
  linear_combination he

/-- The mathematical reduction invariant follows from the source's selected
actual products and literal disagreement, preserving every original factor ID. -/
theorem PairProducts.disagreement {m r : ℕ} (hm : 0<m) {F : SignatureFamily Scalar}
    {G : ActualRepresentatives F m} {labels : Bool → PhaseLabel m} {f : Signature Scalar (2*r+6)}
    (D : PairProducts G labels f) (hd : D.Disagrees) :
    Disagreement m (2*r+4) (Signature.contract (TwoCardLocalization.phaseKernel (labels false)) f)
      (Signature.contract (TwoCardLocalization.phaseKernel (labels true)) f) := by
  rcases hd with hd|⟨hmatch,e,g,heg,he,hg⟩
  · left
    let M₀ : MatchingContractionClosure.Presentation Scalar (Fin (2*r+4)) :=
      ⟨r+2,D.ports false,D.factors false,D.normalizedScalar false⟩
    let M₁ : MatchingContractionClosure.Presentation Scalar (Fin (2*r+4)) :=
      ⟨r+2,D.ports true,D.factors true,D.normalizedScalar true⟩
    refine ⟨M₀,M₁,fun e => (safe_groupM_iff hm _).mpr (D.factors_mem false e),
      fun e => (safe_groupM_iff hm _).mpr (D.factors_mem true e),D.normalizedScalar_ne_zero false,
      D.normalizedScalar_ne_zero true,D.normalized false,D.normalized true,?_⟩
    intro h
    apply hd
    funext u
    exact congrArg (fun M : Equiv.Perm (Fin (2*r+4)) => M u) h
  · right
    let L := MatchingAlignment.ofMate (D.ports false) (D.ports true) (fun u => congrFun hmatch u)
    have hrel : L.factors (D.factors true)=relativeFactor (D.ports false) (D.ports true) (D.factors true) := rfl
    have hA : ∀ e,L.factors (D.factors true) e ∈ groupM m := by
      intro e
      unfold MatchingAlignment.factors
      split
      · exact transpose_group_mem hm (D.factors_mem true _)
      · exact D.factors_mem true _
    have heq : Signature.contract (TwoCardLocalization.phaseKernel (labels true)) f =
        MatchingContractionClosure.productValue (D.ports false) (L.factors (D.factors true)) (D.normalizedScalar true) := by
      rw [D.normalized]
      exact (L.product_eq (D.factors true) (D.normalizedScalar true)).symm
    refine ⟨r+2,D.ports false,D.factors false,L.factors (D.factors true),D.normalizedScalar false,
      D.normalizedScalar true,D.factors_mem false,hA,D.normalizedScalar_ne_zero false,
      D.normalizedScalar_ne_zero true,D.normalized false,heq,e,g,heg,?_,?_⟩
    · simpa only [hrel] using he
    · simpa only [hrel] using hg

end Holant.Dihedral.TwoCardLocalization
