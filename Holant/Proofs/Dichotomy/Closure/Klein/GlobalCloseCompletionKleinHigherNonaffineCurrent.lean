import Holant.Proofs.Closure.ClosureKleinCurrentDeck
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineHighArityFactor
import Holant.Proofs.Algorithms.PrimalityInterfaces

/-! Actual standard-Pauli raw decks produce the literal four-label safe deck.
The Bell overlap proof then excludes prime tensors of every even arity at least ten.
No real-line or amplitude hypothesis is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureKleinCurrent
open scoped BigOperators
namespace Pauli
export Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine (Label xLabel yLabel zLabel E dual)
export Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.MatchingCard (PauliMatchingOrZero OrderedPairSafe)
end Pauli

def pauliLabel (k : Fin 4) : Pauli.Label := ![0,Pauli.xLabel,Pauli.yLabel,Pauli.zLabel] k
def pauliIndex (k : Pauli.Label) : Fin 4 :=
  if k=0 then 0 else if k=Pauli.xLabel then 1 else if k=Pauli.yLabel then 2 else 3
@[simp] theorem pauliLabel_index (k : Pauli.Label) : pauliLabel (pauliIndex k)=k := by
  rcases Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.label_cases k with rfl | rfl | rfl | rfl <;>
    norm_num [pauliLabel,pauliIndex,Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.xLabel,
      Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.yLabel,Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.zLabel]

theorem pauli_E_complex (k : Fin 4) (u v : Bool) :
    (K.E .standard k u v : ℂ)=Pauli.E (pauliLabel k) u v := by
  fin_cases k <;> cases u <;> cases v <;>
    norm_num [pauliLabel,EqualityQuaternary.Klein.E,EqualityQuaternary.Klein.basisQ,
      EqualityQuaternary.Klein.matrix,EqualityQuaternary.Klein.embed_apply,
      EqualityQuaternary.Klein.qI,Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.E,Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.EOver,
      Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.xLabel,Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.yLabel,
      Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.zLabel,imaginaryUnit,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

theorem pauli_dual_complex (k : Fin 4) (u v : Bool) :
    (K.dual .standard k u v : ℂ)=Pauli.dual (pauliLabel k) u v := by
  have indices : pauliLabel (K.theta .standard k)=
      Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.theta (pauliLabel k) := by
    fin_cases k <;> decide
  have half :
      (EqualityQuaternary.Klein.embed EqualityQuaternary.Klein.qHalf : ℂ)=(2 : ℂ)⁻¹ := by
    have h := congrArg CyclicBoundary.AlgebraicRepresentatives.inclusion
      (dualScalarSource_mapped (RingHom.id AlgebraicComplex) .standard (0 : Fin 4)).symm
    change CyclicBoundary.AlgebraicRepresentatives.inclusion
      (EqualityQuaternary.Klein.embed EqualityQuaternary.Klein.qHalf)=
      CyclicBoundary.AlgebraicRepresentatives.inclusion (1/2) at h
    rw [map_div₀,map_one,map_ofNat,one_div] at h
    exact h
  have weight :
      (EqualityQuaternary.Klein.embed (EqualityQuaternary.Klein.dualScalarQ .standard k) : ℂ)=
      (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.d (pauliLabel k))⁻¹ := by
    fin_cases k
    all_goals simpa [pauliLabel,EqualityQuaternary.Klein.dualScalarQ,
      Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.d,Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.dOver,
      Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.xLabel,Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.yLabel,
      Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.zLabel] using half
  have point := congrFun (congrFun (EqualityQuaternary.Klein.dual_scalar .standard k) u) v
  calc
    (K.dual .standard k u v : ℂ)=
        ((EqualityQuaternary.Klein.embed (EqualityQuaternary.Klein.dualScalarQ .standard k)*
          K.E .standard (K.theta .standard k) u v : AlgebraicComplex) : ℂ) :=
      congrArg (fun z : AlgebraicComplex => (z : ℂ)) point
    _=(EqualityQuaternary.Klein.embed (EqualityQuaternary.Klein.dualScalarQ .standard k) : ℂ)*
        (K.E .standard (K.theta .standard k) u v : ℂ) :=
      map_mul CyclicBoundary.AlgebraicRepresentatives.inclusion _ _
    _=(Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.d (pauliLabel k))⁻¹*
        Pauli.E (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.theta (pauliLabel k)) u v := by
      rw [weight,pauli_E_complex,indices]
    _=Pauli.dual (pauliLabel k) u v := rfl

def complexTensor {n : ℕ} (q : Signature AlgebraicComplex n) : Signature ℂ n := fun x => (q x : ℂ)

theorem canonical_pauli {n : ℕ} (q : Signature AlgebraicComplex n)
    (actual : CanonicalMatching .standard q) : Pauli.PauliMatchingOrZero (complexTensor q) := by
  rcases actual with zero | ⟨M,labels,scalar,factors,equation⟩
  · left;funext x;rw [zero];rfl
  · refine Or.inr ⟨M.edges,⟨M.ports⟩,(fun e => pauliLabel (labels e)),(M.scalar : ℂ),?_,?_⟩
    · exact_mod_cast scalar
    · funext x
      change CyclicBoundary.AlgebraicRepresentatives.inclusion (q x)=_
      rw [congrFun equation x]
      simp only [Presentation.tensor,productValue,map_mul,map_prod]
      change (M.scalar : ℂ)*∏ e,
        (M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true))) : ℂ)=_
      simp only [factors,pauli_E_complex,Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.Matching.tensor]

theorem complex_dual_card {n : ℕ} (h : Signature AlgebraicComplex (n+2))
    (order : Equiv.Perm (Fin (n+2))) (k : Fin 4) :
    complexTensor (Signature.contract (K.dual .standard k) (Tensor.reindex order.symm h))=
      Signature.contract (Pauli.dual (pauliLabel k)) (Tensor.reindex order.symm (complexTensor h)) := by
  funext x
  change CyclicBoundary.AlgebraicRepresentatives.inclusion
    (Signature.contract (K.dual .standard k) (Tensor.reindex order.symm h) x)=_
  simp only [Signature.contract,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change (K.dual .standard k u v : ℂ)*(h _ : ℂ)=Pauli.dual (pauliLabel k) u v*(h _ : ℂ)
  rw [pauli_dual_complex]

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (pauli : kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic pauli in
theorem current_pauli_ordered {n : ℕ} (f : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    Pauli.OrderedPairSafe (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f) := by
  intro order label
  have deck := ordered_matching_deck G P torsion cardinal noncyclic f stable order (pauliIndex label)
  rw [pauli] at deck
  have mapped := canonical_pauli _ deck
  rw [complex_dual_card,pauliLabel_index] at mapped
  exact mapped

include cardinal noncyclic pauli in
/-- The actual pauli CURRENT deck supplies the full zero-safe fibre witness
above six. Matching/weights/labels and the zero-card equivalence are conclusions. -/
theorem current_pauli_fibre (r : ℕ) (positive : 0<r) (f : Signature (OI.K G) (2*r+6))
    (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ∃ t : ℕ,∃ M : Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.Matching (Fin (2*r+6)) (t+1),
      ∃ weight : Pauli.Label → ℂ,∃ labels : Pauli.Label → Fin (t+1) → Pauli.Label,
        (∀ a,labels a 0=a) ∧
        RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=
          Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.Fiber.tensor M weight labels ∧
        (∀ a,weight a=0 ↔ Signature.contract (Pauli.dual a)
          (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f)=0) ∧3≤t := by
  have live : RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f≠0 := by
    intro zero
    apply nonzero
    funext x
    apply (ClosurePhysicalBridge.complexEmbedding G).injective
    simpa only [RingHomRealization.mapSignature,map_zero,Pi.zero_apply] using congrFun zero x
  exact Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.MatchingCard.common_full_fiber r positive _ live
    (current_pauli_ordered G P torsion cardinal noncyclic pauli f stable)

include cardinal noncyclic pauli in
theorem stable_prime_arity_le_eight {m : ℕ} (f : Signature (OI.K G) (m+2))
    (even : Even (m+2)) (prime : Prime (⟨m+2,f⟩ : AnySignature (OI.K G)))
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    m+2≤8 := by
  by_contra larger
  obtain ⟨r,hr⟩ := even
  rw [←two_mul] at hr
  have large : 5≤r := by omega
  let phi := ClosurePhysicalBridge.complexEmbedding G
  let fc := RingHomRealization.mapSignature phi f
  have livePrime := PrimalityInterfaces.embedded_prime phi f prime
  have safe := current_pauli_ordered G P torsion cardinal noncyclic pauli f stable
  let e : Fin (m+2) ≃ Fin (2*r) := finCongr hr
  have live : Tensor.reindex e fc≠0 := by
    intro zero
    apply livePrime.1
    have h := congrArg (Tensor.reindex e.symm) zero
    rw [Tensor.reindex_symm] at h
    exact h
  have paired := (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.MatchingCard.pairSafe_iff_ordered fc).mpr safe
  have split := Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.MatchingCard.high_arity_factor r large
    (Tensor.reindex e fc) live
    (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.MatchingCard.pairSafe_reindex e fc paired)
  have original := (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.Fiber.factor_reindex_iff e fc).mp split
  exact livePrime.2 original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineCurrent
