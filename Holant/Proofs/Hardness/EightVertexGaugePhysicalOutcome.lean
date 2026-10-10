import Holant.Proofs.Hardness.EightVertexGaugeThreeDeckBasis
import Holant.Proofs.FiniteGroups.Stabilization.DirectScalars
import Holant.Certificates.EqualityQuaternary.MonomialDeck

/-! A genuine physical alternative for a weighted-even row and the currently
supplied complete monomial representatives: one explicit affine row basis, or
an actual nonzero binary outside all those representative lines. The latter
is left for existing singular/extension machinery; it is not named hardness.
Literal retained I is consumed by the established exact closure theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePhysicalOutcome
open Holant Holant.Tractable Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open EightVertexGaugeTwoRowAlgebra EightVertexGaugePorts EightVertexGaugeAffine
open Holant.OpenNetworkComposition

def row (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex) (i : Fin 3) :
    Signature AlgebraicComplex 4 :=
  (EightVertexGaugeTwoRowNetwork.onPorts (weighted a u) (weighted a u)
    (zeroPair i) (zeroPair i) true).denote

theorem complex_output (a b : AlgebraicComplex) (u v : Fin 4 → AlgebraicComplex)
    (cross : Bool) : complexTensor (output a b u v cross) =
      output (a : ℂ) (b : ℂ) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) cross := by
  funext x
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases cross <;>
    simp [complexTensor,output,table,evenFactor,oddFactor]

theorem complex_row (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex) (i : Fin 3) :
    complexTensor (row a u i) =
      (EightVertexGaugeTwoRowNetwork.onPorts
        (weighted (a : ℂ) (fun j => (u j : ℂ)))
        (weighted (a : ℂ) (fun j => (u j : ℂ)))
        (zeroPair i) (zeroPair i) true).denote := by
  rw [row,onPorts_output,onPorts_output,complex_output]

theorem physical_decks_fourths {m : ℕ} (hm : 3 ≤ m) (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F m) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex) (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (decks : ∀ i : Fin 3, MonomialPhysicalDeck reps (row a u i)) :
    ∀ i, u i ^ 4 = u 0 ^ 4 := by
  have hd (i : Fin 3) := monomial_safeDeck hm reps (row a u i) (decks i)
  simp only [complex_row] at hd
  have h := all_fourth_of_three_decks hm (a : ℂ) (fun j => (u j : ℂ))
    (by exact_mod_cast ha) (fun j => by exact_mod_cast hu j) hd
  intro i
  exact_mod_cast h i 0

theorem physical_decks_basis {m : ℕ} (hm : 3 ≤ m) (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F m) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex) (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (decks : ∀ i : Fin 3, MonomialPhysicalDeck reps (row a u i)) :
    IsCommonKBasis affineClass {⟨4,weighted a u⟩} (diagonalBasis (u 0) (hu 0)) := by
  apply EightVertexGaugeThreeDeckBasis.three_decks_basis hm a u ha hu
  intro i
  rw [← complex_row]
  exact monomial_safeDeck hm reps (row a u i) (decks i)

theorem row_realizes (F : SignatureFamily AlgebraicComplex)
    (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex)
    (member : (⟨4,weighted a u⟩ : AnySignature AlgebraicComplex) ∈ F) (i : Fin 3) :
    Gadget.Realizes F .disequality (row a u i) :=
  EightVertexGaugeTwoRowNetwork.onPorts_realizes _ _ (zeroPair i) (zeroPair i)
    true F member member

/-- The same output can be made from an actual source gadget, rather than
requiring it as a literal supplied label. Retained I makes both closures exact. -/
theorem onPorts_actual (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (M : Signature AlgebraicComplex 4) (actual : Gadget.Realizes F .disequality M)
    (e : Equiv.Perm (Fin 4)) : Gadget.Realizes F .disequality
      (EightVertexGaugeTwoRowNetwork.onPorts M M e e true).denote := by
  have hr := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality M actual e.symm
  simp only [Equiv.symm_symm] at hr
  have ht := Holant.OpenNetworkComposition.realizes_tensor F .disequality _ _ hr hr
  have hw := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ ht
    (EightVertexGaugeTwoRowNetwork.order true).symm
  simp only [Equiv.symm_symm] at hw
  have hc := realizes_contract_exact_of_identity F hI _
    (realizes_contract_exact_of_identity F hI _ hw)
  simpa only [EightVertexGaugeTwoRowNetwork.onPorts,EightVertexGaugeTwoRowNetwork.connect,
    Network.denote_contract,Holant.Complexity.BinaryInterpolation.Chains.reindex_denote,
    Holant.Complexity.BinaryInterpolation.Chains.tensor_denote,Network.denote_corolla] using hc

theorem row_actual (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (a : AlgebraicComplex) (u : Fin 4 → AlgebraicComplex)
    (actual : Gadget.Realizes F .disequality (weighted a u)) (i : Fin 3) :
    Gadget.Realizes F .disequality (row a u i) :=
  onPorts_actual F hI _ actual (zeroPair i)

/-- The physical-card matrix and the existing exact native ordered-card
signature are literally the same finite sum and the same port order. -/
theorem physical_card_signature (q : Signature AlgebraicComplex 4)
    (e : Equiv.Perm (Fin 4)) (B : Holant.Marked.Mat) :
    kernelSignature (physicalCard q e B) = Signature.contract
      (Kernel.mul (Kernel.mul Signature.disequality B) Signature.disequality)
      (Tensor.reindex e.symm q) := by
  funext x
  have hw (a b : Bool) : (Fin.cons a (Fin.cons b x) : Fin 4 → Bool) =
      ![a,b,x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  simp only [kernelSignature,physicalCard,contract0,reorder,
    Signature.contract,Tensor.reindex_apply,hw]
  rfl

theorem physical_card_realizes (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (q : Signature AlgebraicComplex 4) (actual : Gadget.Realizes F .disequality q)
    (e : Equiv.Perm (Fin 4)) (B : Holant.Marked.Mat)
    (hB : Gadget.Realizes F .disequality (kernelSignature B)) :
    Gadget.Realizes F .disequality (kernelSignature (physicalCard q e B)) := by
  rw [physical_card_signature q e B]
  have hmul : Kernel.mul (Kernel.mul Signature.disequality B) Signature.disequality =
      (X*Matrix.of B*X : Binary (K := AlgebraicComplex)) := by
    funext x y
    cases x <;> cases y <;>
      simp [Kernel.mul_apply,Matrix.mul_apply,X,Signature.disequality]
  rw [hmul]
  have hB' : Gadget.Realizes F .disequality
      (Holant.Projective.BoundedTorsion.binarySignature (Matrix.of B : Binary (K := AlgebraicComplex))) := hB
  have hr := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality q actual e
  have hs := realizes_splice F _ _ hr hB' (1 : Fin 4)
  have hc := realizes_contract_exact_of_identity F hI _ hs
  simpa only [close_splice_table] using hc

theorem escape_of_not_decks {m : ℕ}
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex)
    (actualM : Gadget.Realizes F .disequality (weighted a u))
    (decks : ¬ ∀ i : Fin 3, MonomialPhysicalDeck reps (row a u i)) :
    ∃ (i : Fin 3) (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m),
      physicalCard (row a u i) e (reps.matrix p t) ≠ 0 ∧
      ¬ ActualMonomialLine reps (physicalCard (row a u i) e (reps.matrix p t)) ∧
      Gadget.Realizes F .disequality
        (kernelSignature (physicalCard (row a u i) e (reps.matrix p t))) := by
  simp only [MonomialPhysicalDeck] at decks
  push Not at decks
  obtain ⟨i,e,p,t,nonzero,outside⟩ := decks
  exact ⟨i,e,p,t,nonzero,outside,
    physical_card_realizes F hI _ (row_actual F hI a u actualM i) e _ (reps.actual p t)⟩

/-- This alternative assumes neither safety of a newly constructed row nor
any target-class oracle. The right branch supplies an actual binary over the
same F, with its actual representative and exact original scalar untouched. -/
theorem basis_or_physical_escape {m : ℕ} (hm : 3 ≤ m)
    (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (reps : MonomialRepresentatives F m) (a : AlgebraicComplex)
    (u : Fin 4 → AlgebraicComplex) (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (actualM : Gadget.Realizes F .disequality (weighted a u)) :
    IsCommonKBasis affineClass {⟨4,weighted a u⟩} (diagonalBasis (u 0) (hu 0)) ∨
      ∃ (i : Fin 3) (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m),
        physicalCard (row a u i) e (reps.matrix p t) ≠ 0 ∧
        ¬ ActualMonomialLine reps (physicalCard (row a u i) e (reps.matrix p t)) ∧
        Gadget.Realizes F .disequality
          (kernelSignature (physicalCard (row a u i) e (reps.matrix p t))) := by
  classical
  by_cases decks : ∀ i : Fin 3, MonomialPhysicalDeck reps (row a u i)
  · exact Or.inl (physical_decks_basis hm F reps a u ha hu decks)
  · simp only [MonomialPhysicalDeck] at decks
    push Not at decks
    obtain ⟨i,e,p,t,nonzero,outside⟩ := decks
    exact Or.inr ⟨i,e,p,t,nonzero,outside,
      physical_card_realizes F hI _ (row_actual F hI a u actualM i) e _ (reps.actual p t)⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePhysicalOutcome
end
