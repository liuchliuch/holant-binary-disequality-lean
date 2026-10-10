import Holant.Proofs.Tetrahedral.ExternalOddCompletion.Loops
import Holant.Proofs.Reductions.GeneralExtraction.SupportDescent
import Holant.Proofs.Reductions.GeneralExtraction.SupportCaps
import Holant.ReedMuller.CoefficientAtlas.ContractionTransport
import Holant.Tractable.KPresentation
import Holant.NetworkAlgebra


noncomputable section
namespace Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure
open Holant.OpenNetworkComposition.ProjectiveSubstitution
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportDescent
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
open Holant.ReedMuller.CoefficientAtlas
set_option backward.isDefEq.respectTransparency false

/-- Odd arity forbids balance zero, including for nonsymmetric tensors. -/
theorem odd_balance_ne_zero {n : ℕ} (ho : Odd n) (x : Fin n → Bool) :
    balance true x ≠ 0 := by
  have hb := balance_count true x
  obtain ⟨k,hk⟩ := ho
  simp only [Fintype.card_fin] at hb
  omega

/-- Every supported mixed word forces a nonzero X pair closure. The third
triangle branch is retained when the first two trials cancel. -/
theorem native_noCuts_constant {k : ℕ} (f : Signature AlgebraicComplex (k+2))
    (ho : Odd (k+2)) (hn : 3≤k+2)
    (hz : ∀ p : Equiv.Perm (Fin (k+2)),
      Signature.contract Signature.disequality (Tensor.reindex p f)=0)
    (x : Fin (k+2) → Bool) (hx : f x≠0) :
    x=(fun _ => false) ∨ x=(fun _ => true) := by
  by_contra hconstant
  have hfalse : x≠fun _ => false := fun h => hconstant (Or.inl h)
  have htrue : x≠fun _ => true := fun h => hconstant (Or.inr h)
  have hb := odd_balance_ne_zero ho x
  obtain ⟨b,hbpos⟩ : ∃ b : Bool,0<balance b x := by
    by_cases h : 0<balance true x
    · exact ⟨true,h⟩
    · refine ⟨false,?_⟩
      have he := balance_negate true x
      simp only [Bool.not_true] at he
      omega
  have hm : ∃ i,x i≠b := by
    by_contra h
    push_neg at h
    have he : x=fun _ => b := funext h
    cases b
    · exact hfalse he
    · exact htrue he
  obtain ⟨i,j,hij,y,hy,_⟩ := exact_contraction (by norm_num : (2:AlgebraicComplex)≠0)
    b f x hx (le_of_lt hbpos) (by simp only [Fintype.card_fin]; omega) hm
  have hc := remaining_card i j hij
  simp only [Fintype.card_fin] at hc
  have hcard : Fintype.card (Remaining i j)=k := by omega
  let r : Remaining i j ≃ Fin k := (Fintype.equivFin _).trans (finCongr hcard)
  have he := contractPair_ordered i j hij r f
  rw [hz] at he
  have hyzero := congrFun he (fun t => y (r.symm t))
  have heq : contractPair i j Signature.disequality f y=0 := by
    simpa only [Tensor.reindex,Function.comp_def,Equiv.symm_apply_apply,Pi.zero_apply] using hyzero
  exact hy heq

/-- Ordinary loop annihilation transports to native-X loop annihilation.
The exact K matrix satisfies KᵀK=X; no unitary/conjugate assertion is used. -/
theorem ordinary_noCuts_native {k : ℕ} (f : Signature AlgebraicComplex (k+2))
    (hz : ∀ p : Equiv.Perm (Fin (k+2)),
      Signature.contract Signature.equality (Tensor.reindex p f)=0) :
    ∀ p : Equiv.Perm (Fin (k+2)),
      Signature.contract Signature.disequality
        (Tensor.reindex p (sourceKBasis.symm.action f))=0 := by
  intro p
  let g := sourceKBasis.symm.action f
  have hrestore : sourceKBasis.action g=f := sourceKBasis.action_symm_action f
  have he : sourceKBasis.action
      (Signature.contract Signature.disequality (Tensor.reindex p g))=
      Signature.contract Signature.equality (Tensor.reindex p f) := by
    calc
      _ = Signature.contract Signature.equality
          (Signature.coordinateAction (fun _ => sourceKBasis.matrix) (Tensor.reindex p g)) := by
        simpa only [InvertibleKernel.action,sourceKBasis_pullback] using
          (coordinateAction_contract sourceKBasis.matrix Signature.equality
            (Tensor.reindex p g)).symm
      _ = _ := by
        rw [coordinateAction_reindex]
        change Signature.contract Signature.equality (Tensor.reindex p (sourceKBasis.action g))=_
        rw [hrestore]
  have hzero := congrArg sourceKBasis.symm.action (he.trans (hz p))
  rw [InvertibleKernel.symm_action_action] at hzero
  simpa only [g,InvertibleKernel.action,
    Signature.coordinateAction_zero] using hzero

/-- A direct obstruction theorem for a NONZERO actual ordinary terminal.
This conclusion is about that tensor, not a classification of its whole family. -/
theorem ordinary_terminal_support {n : ℕ} (f : Signature AlgebraicComplex n)
    (ho : Odd n) (hn : 3≤n) (hz : Loops.NoCuts f) :
    ∀ x,sourceKBasis.symm.action f x≠0 →
      x=(fun _ => false) ∨ x=(fun _ => true) := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+2 := ⟨n-2,by omega⟩
  have heq : ∀p : Equiv.Perm (Fin (k+2)),
      Signature.contract Signature.equality (Tensor.reindex p f)=0 := by
    intro p
    have h := hz k rfl p
    change Signature.contract Signature.equality
      (Tensor.reindex p (Tensor.reindex (Equiv.refl _) f))=0 at h
    simpa only [Tensor.reindex_refl] using h
  exact native_noCuts_constant _ ho hn (ordinary_noCuts_native f heq)

def twoConstants {n : ℕ} (c₀ c₁ : AlgebraicComplex) : Signature AlgebraicComplex n :=
  purePin c₀ false n+purePin c₁ true n

/-- The two actual endpoint coefficients are retained; neither is implicitly
normalized to one. One may vanish, so this does not assert a usable equality. -/
theorem ordinary_terminal_decomposition {n : ℕ} (f : Signature AlgebraicComplex n)
    (ho : Odd n) (hn : 3≤n) (hz : Loops.NoCuts f) :
    sourceKBasis.symm.action f=twoConstants
      (sourceKBasis.symm.action f (fun _ => false))
      (sourceKBasis.symm.action f (fun _ => true)) := by
  let g := sourceKBasis.symm.action f
  have hdistinct : (fun _ : Fin n => false)≠(fun _ => true) := by
    intro h
    have he := congrFun h (⟨0,by omega⟩ : Fin n)
    cases he
  funext x
  by_cases hfalse : x=fun _ => false
  · simp [twoConstants,purePin,hfalse,hdistinct]
  by_cases htrue : x=fun _ => true
  · simp [twoConstants,purePin,htrue,Ne.symm hdistinct]
  · have hzero : g x=0 := by
      by_contra hx
      rcases ordinary_terminal_support f ho hn hz x hx with h | h
      · exact hfalse h
      · exact htrue h
    simp [twoConstants,purePin,hfalse,htrue,g] at hzero ⊢
    exact hzero

/-- Ring embeddings preserve the same ordinary cut equations. This is the
only field transport used for the diagnostic classification. -/
theorem map_noCuts {L : Type} [Field L] (φ : L →+* AlgebraicComplex)
    {n : ℕ} (f : Signature L n) (hz : Loops.NoCuts f) :
    Loops.NoCuts (fun x => φ (f x)) := by
  intro k hk p
  subst n
  funext x
  have he := congrArg φ (congrFun (hz k rfl p) x)
  simpa [Signature.contract_equality,Signature.contract,Tensor.reindex,
    Signature.equality,Fintype.sum_bool] using he

end Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure
