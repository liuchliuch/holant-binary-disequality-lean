import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineCurrent
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineEightLabels
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineBellNorm
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramCurrent

/-! Actual real normalization and the genuine two-copy Gram alternative give
one scalar and four signs for the translated Bell fiber. The other alternative
is a nonzero nonmatching quaternary over the unchanged original source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineEightNorm
open Holant Holant.Tractable Holant.Algebraic
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Dihedral.CompatibleCoefficientLine (pair tail)
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
open scoped BigOperators

private theorem pair_eight (u : Fin 2→Bool) (z : Fin 6→Bool) :
    pair (u 0) (u 1) z=Fin.addCases (m:=2) (n:=6) u z := by
  funext i
  fin_cases i <;> rfl

private theorem complex_gram (f : Signature ℂ 8) (r : Signature ℝ 8) (c : ℂ)
    (normal : f=fun x=>c*(r x:ℂ)) (d : ℝ)
    (orthogonal : ∀u v : Fin 2→Bool,
      (∑z : Fin 6→Bool,r (Fin.addCases (m:=2) (n:=6) u z)*r (Fin.addCases (m:=2) (n:=6) v z))=if u=v then d else 0) :
    ∀u v : Fin 2→Bool,
      (∑z : Fin 6→Bool,f (pair (u 0) (u 1) z)*f (pair (v 0) (v 1) z))=
        if u=v then c^2*(d:ℂ) else 0 := by
  intro u v
  rw [normal]
  simp only [pair_eight]
  have term (z : Fin 6→Bool) :
      (c*(r (Fin.addCases (m:=2) (n:=6) u z):ℂ))*(c*(r (Fin.addCases (m:=2) (n:=6) v z):ℂ))=
        c^2*((r (Fin.addCases (m:=2) (n:=6) u z)*r (Fin.addCases (m:=2) (n:=6) v z):ℝ):ℂ) := by
    rw [Complex.ofReal_mul]
    ring
  simp_rw [term]
  rw [←Finset.mul_sum,←Complex.ofReal_sum,orthogonal]
  split_ifs <;> simp

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureKleinCurrent.kind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem normal_or_quaternary (f : Signature (OI.K G) 8)
    (prime : Prime (⟨8,f⟩ : AnySignature (OI.K G)))
    (actual : Gadget.Realizes P.family .disequality f)
    (stable : ∀g∈rawDeck P.family torsion f,MatchingOrZero (actualTransfers P.family) g)
    (r : Signature ℝ 8) (c : ℂ) (hc : c≠0)
    (normal : RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=
      fun x=>c*(r x:ℂ)) :
    (∃M : Matching (Fin 8) 4,∃scale : ℂ,∃phase : Label→Bool,∃shifts : Fin 4→Label,
      scale≠0 ∧ phase 0=false ∧ shifts 0=0 ∧
      RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=
        Fiber.tensor M (fun a=>scale*(if phase a then -1 else 1)) (fun a e=>a+shifts e)) ∨
    ∃q : Signature (OI.K G) 4,q≠0 ∧ Gadget.Realizes P.family .disequality q ∧
      ¬MatchingOrZero (actualTransfers P.family) q := by
  classical
  rcases GlobalCloseCompletionKleinGramCurrent.orthogonal_or_quaternary
    G P torsion cardinal noncyclic standard f (by decide : 0<6) prime actual r c hc normal with norm|q
  · left
    obtain ⟨d,_positive,orthogonal⟩ := norm
    let phi := ClosurePhysicalBridge.complexEmbedding G
    let fc := RingHomRealization.mapSignature phi f
    have livePrime := PrimalityInterfaces.embedded_prime phi f prime
    have safe := Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineCurrent.current_pauli_ordered
      G P torsion cardinal noncyclic standard f stable
    obtain ⟨t,M,weight,labels,forms,_zeros⟩ :=
      MatchingCard.common_card_coordinates 1 (by decide) fc livePrime.1 safe
    have card := M.port_card
    simp only [Fintype.card_fin] at card
    have three : t=3 := by omega
    subst t
    have squares := BellNorm.coefficient_squares fc (c^2*(d:ℂ))
      (complex_gram fc r c normal d orthogonal) M weight labels forms
    let fullLabels : Label→Fin 4→Label := fun a=>Fin.cons a (labels a)
    have equation : fc=Fiber.tensor M.prepend weight fullLabels := by
      funext x
      have hx : pair (x 0) (x 1) (tail x)=x := by
        funext i
        refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i <;> rfl
      have hh := MatchingCard.front_reconstruction fc (x 0) (x 1) (tail x)
      rw [hx] at hh
      rw [←hh]
      simp only [Fiber.tensor,fullLabels,Matching.prepend_tensor,forms]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have pairSafe : MatchingCard.PairSafe (Fiber.tensor M.prepend weight fullLabels) := by
      rw [←equation]
      exact (MatchingCard.pairSafe_iff_ordered fc).mpr safe
    have live : Fiber.tensor M.prepend weight fullLabels≠0 := by
      rw [←equation]
      exact livePrime.1
    have noFactor : ¬Fiber.HasProperTensorFactor (Fiber.tensor M.prepend weight fullLabels) := by
      rw [←equation]
      exact livePrime.2
    obtain ⟨weights,bijective⟩ := Fiber.dichotomy M.prepend (by decide) weight fullLabels 0
      (fun _=>rfl) pairSafe live noFactor
    let perms : Fin 4→Equiv.Perm Label := fun e=>Equiv.ofBijective (fun a=>fullLabels a e) (bijective e)
    have shifted := Fiber.label_translations M.prepend weight perms (fun _=>rfl) weights pairSafe
    let phase : Label→Bool := fun a=>decide (weight a≠weight 0)
    have signs (a : Label) : weight a=weight 0*(if phase a then -1 else 1) := by
      by_cases equal : weight a=weight 0
      · simp [phase,equal]
      · have opposite := (sq_eq_sq_iff_eq_or_eq_neg.mp (squares a)).resolve_left equal
        simp [phase,equal,opposite]
    refine ⟨M.prepend,weight 0,phase,(fun e=>perms e 0),weights 0,by simp [phase],rfl,?_⟩
    change fc=Fiber.tensor M.prepend (fun a=>weight 0*(if phase a then -1 else 1))
      (fun a e=>a+perms e 0)
    rw [equation]
    congr 1
    · funext a
      exact signs a
    · funext a e
      exact shifted e a
  · exact Or.inr q

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineEightNorm
end
