import Holant.Proofs.Closure.ClosureKleinCurrentDeck
import Holant.Pauli.ProjectiveDetermination.Determination
import Holant.Dihedral.TwoCardLocalization.ResidualOrder

/-! The genuine standard-Pauli matching deck forces a higher current tensor
onto one real line. Ordered source cards are related to every original-port
Pauli measurement before the projective-determination theorem is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardRealLine
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Pauli.ProjectiveDetermination
open Holant.Dihedral.TwoCardLocalization
open Holant.Dihedral.CompatibleClosure (pairOrder)
open scoped BigOperators
namespace K
export EqualityQuaternary.Klein (E dual)
end K
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

abbrev inclusion : AlgebraicComplex→+*ℂ := CyclicBoundary.AlgebraicRepresentatives.inclusion

theorem realLine_precompose {α β : Type*} {f : α→ℂ} (h : IsRealLine f) (p : β→α) :
    IsRealLine (fun x=>f (p x)) := by
  obtain ⟨c,hc,r,rfl⟩ := h
  exact ⟨c,hc,fun x=>r (p x),rfl⟩

theorem realLine_scale {α : Type*} {f : α→ℂ} (h : IsRealLine f) (c : ℂ) (hc : c≠0) :
    IsRealLine (fun x=>c*f x) := by
  obtain ⟨d,hd,r,rfl⟩ := h
  refine ⟨c*d,mul_ne_zero hc hd,r,?_⟩
  funext x
  ring

private theorem insertPair_fill {P : Type*} [DecidableEq P] (u v : P) (hne : u≠v)
    (a b : Bool) (x : Remaining u v→Bool) :
    insertPair u v a b (extendRemaining u v x)=fill u v a b x := by
  funext i
  by_cases hi : i=u
  · subst i; simp [insertPair,fill,hne]
  by_cases hj : i=v
  · subst i; simp [insertPair,fill,Ne.symm hne]
  simp [insertPair,extendRemaining,fill,hi,hj]

theorem card_order {n : ℕ} (u v : Fin (n+2)) (hne : u≠v) (k : Label) (f : Signature ℂ (n+2)) :
    Tensor.reindex (remainingOrder u v hne).symm (card u v k f)=
      Signature.contract (kernel k) (Tensor.reindex (pairOrder u v).symm f) := by
  have eq : card u v k f=contractPair u v (Matrix.of (kernel k)) f := by
    funext x
    simp only [card,contractPair,insertPair_fill u v hne,Matrix.of_apply]
  rw [eq]
  exact contractPair_order u v hne (kernel k) f

theorem ordered_realLine {n : ℕ} (f : Signature ℂ (n+2)) (large : 5≤n+2)
    (cards : ∀order : Equiv.Perm (Fin (n+2)),∀k : Label,
      IsRealLine (Signature.contract (kernel k) (Tensor.reindex order.symm f))) : IsRealLine f := by
  apply pauli_real_line (n+2) large f
  intro u v huv k
  have h := cards (pairOrder u v) k
  rw [←card_order u v (ne_of_lt huv) k f] at h
  have h' := realLine_precompose h (fun x : Remaining u v→Bool=>fun i=>x (remainingOrder u v (ne_of_lt huv) i))
  simpa only [Tensor.reindex_apply,Equiv.apply_symm_apply] using h'

theorem E_real (k : Fin 4) (b c : Bool) :
    (((inclusion (K.E .standard k b c)).re : ℝ) : ℂ)=inclusion (K.E .standard k b c) := by
  fin_cases k <;> cases b <;> cases c <;>
    norm_num [K.E,EqualityQuaternary.Klein.basisQ,EqualityQuaternary.Klein.matrix,
      EqualityQuaternary.Klein.embed_apply,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

theorem canonical_real {n : ℕ} (f : Signature AlgebraicComplex n)
    (matching : ClosureKleinCurrent.CanonicalMatching .standard f) :
    IsRealLine (RingHomRealization.mapSignature inclusion f) := by
  rcases matching with rfl|⟨M,labels,hc,matrices,rfl⟩
  · exact ⟨1,one_ne_zero,fun _=>0,by funext x; simp [RingHomRealization.mapSignature]⟩
  refine ⟨inclusion M.scalar,(map_ne_zero _).mpr hc,
    (fun x=>∏e,(inclusion (K.E .standard (labels e) (x (M.ports (e,false))) (x (M.ports (e,true))))).re),?_⟩
  funext x
  simp only [RingHomRealization.mapSignature,Presentation.tensor,productValue,map_mul,map_prod,matrices]
  rw [Complex.ofReal_prod]
  simp only [E_real]

def index (k : Label) : Fin 4 := ![0,2,1,3] k

theorem dual_kernel (k : Label) (b c : Bool) :
    2*inclusion (K.dual .standard (index k) b c)=kernel k b c := by
  fin_cases k <;> cases b <;> cases c <;>
    norm_num [index,kernel,K.dual,EqualityQuaternary.Klein.dualQ,EqualityQuaternary.Klein.matrix,
      EqualityQuaternary.Klein.embed_apply,EqualityQuaternary.Klein.qHalf]
  all_goals change (2 : ℂ)*(2 : ℂ)⁻¹=1
  all_goals norm_num

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem current_realLine {n : ℕ} (f : Signature (OI.K G) (n+2)) (large : 5≤n+2)
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g) :
    IsRealLine (RingHomRealization.mapSignature (inclusion.comp (ClosureSourceRows.embedding G)) f) := by
  apply ordered_realLine _ large
  intro order k
  have matching := ClosureKleinCurrent.ordered_matching_deck G P torsion cardinal noncyclic f stable order (index k)
  rw [standard] at matching
  have real := canonical_real _ matching
  have twice := realLine_scale real 2 (by norm_num)
  convert twice using 1
  funext x
  simp only [RingHomRealization.mapSignature,Signature.contract,map_sum,map_mul,
    Tensor.reindex_apply,RingHom.comp_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [←mul_assoc,dual_kernel]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardRealLine
end
