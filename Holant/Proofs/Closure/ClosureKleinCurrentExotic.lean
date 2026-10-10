import Holant.Proofs.Closure.ClosureKleinCurrentDeck
import Holant.Pauli.ExoticKlein.FiberFactor
import Holant.Pauli.ExoticKlein.MatchingFour

/-! Honest CURRENT exotic OrderedPairSafe and the frozen closed ≥8-port
common-fibre producer. This does not claim a six-port classifier or supply a
constant-label hypothesis to the fibre factor theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open scoped BigOperators
namespace Exotic
export Holant.Pauli.ExoticKlein (Label xLabel yLabel zLabel E dual)
export Holant.Pauli.ExoticKlein.MatchingCard (ExoticMatchingOrZero OrderedPairSafe)
end Exotic

def exoticLabel (k : Fin 4) : Exotic.Label := ![0,Exotic.xLabel,Exotic.yLabel,Exotic.zLabel] k
def exoticIndex (k : Exotic.Label) : Fin 4 :=
  if k=0 then 0 else if k=Exotic.xLabel then 1 else if k=Exotic.yLabel then 2 else 3
@[simp] theorem exoticLabel_index (k : Exotic.Label) : exoticLabel (exoticIndex k)=k := by
  rcases Holant.Pauli.ExoticKlein.label_cases k with rfl | rfl | rfl | rfl <;>
    norm_num [exoticLabel,exoticIndex,Holant.Pauli.ExoticKlein.xLabel,
      Holant.Pauli.ExoticKlein.yLabel,Holant.Pauli.ExoticKlein.zLabel]

theorem exotic_E_complex (k : Fin 4) (u v : Bool) :
    (K.E .exotic k u v : ℂ)=Exotic.E (exoticLabel k) u v := by
  fin_cases k <;> cases u <;> cases v <;>
    norm_num [exoticLabel,EqualityQuaternary.Klein.E,EqualityQuaternary.Klein.basisQ,
      EqualityQuaternary.Klein.matrix,EqualityQuaternary.Klein.embed_apply,
      EqualityQuaternary.Klein.qI,Holant.Pauli.ExoticKlein.E,Holant.Pauli.ExoticKlein.EOver,
      Holant.Pauli.ExoticKlein.xLabel,Holant.Pauli.ExoticKlein.yLabel,
      Holant.Pauli.ExoticKlein.zLabel,imaginaryUnit,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

theorem exotic_dual_complex (k : Fin 4) (u v : Bool) :
    (K.dual .exotic k u v : ℂ)=Exotic.dual (exoticLabel k) u v := by
  have indices : exoticLabel (K.theta .exotic k)=
      Holant.Pauli.ExoticKlein.theta (exoticLabel k) := by
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
  have quarter :
      (EqualityQuaternary.Klein.embed EqualityQuaternary.Klein.qQuarter : ℂ)=(4 : ℂ)⁻¹ := by
    have h := congrArg CyclicBoundary.AlgebraicRepresentatives.inclusion
      (dualScalarSource_mapped (RingHom.id AlgebraicComplex) .exotic (2 : Fin 4)).symm
    change CyclicBoundary.AlgebraicRepresentatives.inclusion
      (EqualityQuaternary.Klein.embed EqualityQuaternary.Klein.qQuarter)=
      CyclicBoundary.AlgebraicRepresentatives.inclusion (1/4) at h
    rw [map_div₀,map_one,map_ofNat,one_div] at h
    exact h
  have weight :
      (EqualityQuaternary.Klein.embed (EqualityQuaternary.Klein.dualScalarQ .exotic k) : ℂ)=
      (Holant.Pauli.ExoticKlein.d (exoticLabel k))⁻¹ := by
    fin_cases k
    all_goals simpa [exoticLabel,EqualityQuaternary.Klein.dualScalarQ,
      Holant.Pauli.ExoticKlein.d,Holant.Pauli.ExoticKlein.dOver,
      Holant.Pauli.ExoticKlein.xLabel,Holant.Pauli.ExoticKlein.yLabel,
      Holant.Pauli.ExoticKlein.zLabel] using (by first | exact half | exact quarter)
  have point := congrFun (congrFun (EqualityQuaternary.Klein.dual_scalar .exotic k) u) v
  calc
    (K.dual .exotic k u v : ℂ)=
        ((EqualityQuaternary.Klein.embed (EqualityQuaternary.Klein.dualScalarQ .exotic k)*
          K.E .exotic (K.theta .exotic k) u v : AlgebraicComplex) : ℂ) :=
      congrArg (fun z : AlgebraicComplex => (z : ℂ)) point
    _=(EqualityQuaternary.Klein.embed (EqualityQuaternary.Klein.dualScalarQ .exotic k) : ℂ)*
        (K.E .exotic (K.theta .exotic k) u v : ℂ) :=
      map_mul CyclicBoundary.AlgebraicRepresentatives.inclusion _ _
    _=(Holant.Pauli.ExoticKlein.d (exoticLabel k))⁻¹*
        Exotic.E (Holant.Pauli.ExoticKlein.theta (exoticLabel k)) u v := by
      rw [weight,exotic_E_complex,indices]
    _=Exotic.dual (exoticLabel k) u v := rfl

def complexTensor {n : ℕ} (q : Signature AlgebraicComplex n) : Signature ℂ n := fun x => (q x : ℂ)

theorem canonical_exotic {n : ℕ} (q : Signature AlgebraicComplex n)
    (actual : CanonicalMatching .exotic q) : Exotic.ExoticMatchingOrZero (complexTensor q) := by
  rcases actual with zero | ⟨M,labels,scalar,factors,equation⟩
  · left;funext x;rw [zero];rfl
  · refine Or.inr ⟨M.edges,⟨M.ports⟩,(fun e => exoticLabel (labels e)),(M.scalar : ℂ),?_,?_⟩
    · exact_mod_cast scalar
    · funext x
      change CyclicBoundary.AlgebraicRepresentatives.inclusion (q x)=_
      rw [congrFun equation x]
      simp only [Presentation.tensor,productValue,map_mul,map_prod]
      change (M.scalar : ℂ)*∏ e,
        (M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true))) : ℂ)=_
      simp only [factors,exotic_E_complex,Holant.Pauli.ExoticKlein.Matching.tensor]

theorem complex_dual_card {n : ℕ} (h : Signature AlgebraicComplex (n+2))
    (order : Equiv.Perm (Fin (n+2))) (k : Fin 4) :
    complexTensor (Signature.contract (K.dual .exotic k) (Tensor.reindex order.symm h))=
      Signature.contract (Exotic.dual (exoticLabel k)) (Tensor.reindex order.symm (complexTensor h)) := by
  funext x
  change CyclicBoundary.AlgebraicRepresentatives.inclusion
    (Signature.contract (K.dual .exotic k) (Tensor.reindex order.symm h) x)=_
  simp only [Signature.contract,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change (K.dual .exotic k u v : ℂ)*(h _ : ℂ)=Exotic.dual (exoticLabel k) u v*(h _ : ℂ)
  rw [exotic_dual_complex]

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (exotic : kind G P torsion cardinal noncyclic=.exotic)

include cardinal noncyclic exotic in
theorem current_exotic_ordered {n : ℕ} (f : Signature (OI.K G) (n+2))
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    Exotic.OrderedPairSafe (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f) := by
  intro order label
  have deck := ordered_matching_deck G P torsion cardinal noncyclic f stable order (exoticIndex label)
  rw [exotic] at deck
  have mapped := canonical_exotic _ deck
  rw [complex_dual_card,exoticLabel_index] at mapped
  exact mapped

include cardinal noncyclic exotic in
/-- The actual exotic CURRENT deck supplies the full zero-safe fibre witness
above six. Matching/weights/labels and the zero-card equivalence are conclusions. -/
theorem current_exotic_fibre (r : ℕ) (positive : 0<r) (f : Signature (OI.K G) (2*r+6))
    (nonzero : f≠0)
    (stable : ∀ g ∈ rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    ∃ t : ℕ,∃ M : Holant.Pauli.ExoticKlein.Matching (Fin (2*r+6)) (t+1),
      ∃ weight : Exotic.Label → ℂ,∃ labels : Exotic.Label → Fin (t+1) → Exotic.Label,
        (∀ a,labels a 0=a) ∧
        RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=
          Holant.Pauli.ExoticKlein.Fiber.tensor M weight labels ∧
        (∀ a,weight a=0 ↔ Signature.contract (Exotic.dual a)
          (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f)=0) ∧3≤t := by
  have live : RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f≠0 := by
    intro zero
    apply nonzero
    funext x
    apply (ClosurePhysicalBridge.complexEmbedding G).injective
    simpa only [RingHomRealization.mapSignature,map_zero,Pi.zero_apply] using congrFun zero x
  exact Holant.Pauli.ExoticKlein.MatchingCard.common_full_fiber r positive _ live
    (current_exotic_ordered G P torsion cardinal noncyclic exotic f stable)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinCurrent
