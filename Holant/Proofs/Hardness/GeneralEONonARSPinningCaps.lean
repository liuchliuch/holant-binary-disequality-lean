import Holant.Proofs.Hardness.GeneralEONonARSPinningGraph
import Holant.Proofs.Hardness.GeneralEONonARSPinningSource

/-! A finite original-coefficient hardness branch in the non-ARS pinning task.
The selector checks every original row and every native self-loop matching
leaving four ordered ports. Failure of literal EOTract for one resulting
coefficient table supplies a full counting programme over the original family.
No existence of such a cap is inferred merely from failure of ARS. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningCaps
open Computability Holant Holant.Complexity Holant.Algebraic Holant.Tractable
open FixedGadgetSubstitution
open scoped BigOperators
namespace N
export GeneralEONonARSPinningGraph (graph assignment denote_coefficients central arity_eq)
end N
namespace B
export GeneralEONonARSPinningFieldBridge (query query_counts)
end B
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
attribute [local irreducible] GeneralEONonARSPinningSource.source
variable {s r : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (j : Fin s) (e : Fin (a j.val) ≃ (Fin 4 ⊕ (Fin r × Bool)))
local instance targetAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

def coefficient (x : Fin 4 → Bool) : AlgebraicComplex :=
  ∑z : (Fin r × Bool) → Bool, G j (N.assignment e x z) *
    ∏i : Fin r, Signature.disequality (z (i,false)) (z (i,true))

abbrev graph := N.graph e (G j)

theorem denote : (graph G j e).denote=coefficient G j e := by
  funext x
  exact N.denote_coefficients e (G j) x

def labels : Labelling (graph G j e).shape s 1 a where
  vertex _ := j
  vertex_arity _ := rfl
  edge _ := 0

theorem exact : LabelledNetwork.Exact G (graph G j e) (labels G j e) := fun _ => rfl
theorem native : ∀k,(graph G j e).edge k=Signature.disequality := fun _ => rfl

variable (he : Signature.CentralSupport (G j)) (ht : ¬EOTract {⟨4,coefficient G j e⟩})
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    f (O.originalValue G) :=
  GeneralEONonARSPinningSource.source G (graph G j e) (labels G j e)
    (exact G j e) (native G j e) (N.central e (G j) he)
    (by simpa only [denote] using ht) w

include j e he ht in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (O.originalValue G) := by
  intro α ea f w
  exact ⟨(source G j e he ht w).reduction⟩

/-- Six explicit nonzero coefficient sums are sufficient: complementary
supported triples violate the two possible common charge signs. -/
theorem dense_not_tract (M : Signature AlgebraicComplex 4)
    (hc : Signature.CentralSupport M) (hd : ∀x,weight x=2 → M x≠0) :
    ¬EOTract {⟨4,M⟩} := by
  rintro ⟨_,_,sign,C,closed,_⟩
  cases sign
  · have ht := closed ⟨4,M⟩ (by simp)
      ![true,true,false,false] ![true,false,true,false] ![false,true,true,false]
      (hd _ (by decide)) (hd _ (by decide)) (hd _ (by decide))
    rcases ht with ht | ht
    · exact ht (hc _ (by change (2*0 : ℕ)≠4; decide))
    · have hw : charge (tripleXor ![true,true,false,false]
          ![true,false,true,false] ![false,true,true,false])= -4 := by decide
      rw [hw] at ht
      norm_num [EOSign.value] at ht
  · have ht := closed ⟨4,M⟩ (by simp)
      ![false,false,true,true] ![false,true,false,true] ![true,false,false,true]
      (hd _ (by decide)) (hd _ (by decide)) (hd _ (by decide))
    rcases ht with ht | ht
    · exact ht (hc _ (by change (2*4 : ℕ)≠4; decide))
    · have hw : charge (tripleXor ![false,false,true,true]
          ![false,true,false,true] ![true,false,false,true])=4 := by decide
      rw [hw] at ht
      norm_num [EOSign.value] at ht

def denseSource (hd : ∀x,weight x=2 → coefficient G j e x≠0) (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool
      (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
      f (O.originalValue G) :=
  source G j e he (dense_not_tract (coefficient G j e)
    (by rw [←denote]; exact N.central e (G j) he) hd) w

def query := B.query G (graph G j e) (labels G j e)

/-- One original vertex per source occurrence; precisely r additional native
loops per occurrence, plus the source's original edges. -/
theorem query_counts (q : ExactSignatureTables.Input 1 1 (fun _ => 4)) :
    (query G j e q).val.vertices.length=q.val.vertices.length ∧
    (query G j e q).val.edges.length=q.val.edges.length+q.val.vertices.length*r := by
  have h := B.query_counts G (graph G j e) (labels G j e) q
  change (query G j e q).val.vertices.length=q.val.vertices.length*1 ∧
    (query G j e q).val.edges.length=q.val.edges.length+q.val.vertices.length*r at h
  simpa only [Nat.mul_one] using h

/-- Only literal original coefficients and a complete finite port matching
are searched. An absent or too-small arity cannot supply a choice. -/
abbrev Choice (s : ℕ) (a : ℕ → ℕ) :=
  (j : Fin s) × (Fin (a j.val) ≃ (Fin 4 ⊕ (Fin (a j.val/2-2) × Bool)))

noncomputable instance choiceFintype : Fintype (Choice s a) := inferInstance

def Applicable : Prop := ∃c : Choice s a,
  Signature.CentralSupport (G c.1) ∧ ¬EOTract {⟨4,coefficient G c.1 c.2⟩}

include he ht in
theorem applicable_of_coefficients : Applicable G := by
  have hn := N.arity_eq e
  have hr : r=a j.val/2-2 := by omega
  subst r
  exact ⟨⟨j,e⟩,he,ht⟩

def selected (h : Applicable G) : Choice s a := Classical.choose h

theorem selected_spec (h : Applicable G) :
    Signature.CentralSupport (G (selected G h).1) ∧
      ¬EOTract {⟨4,coefficient G (selected G h).1 (selected G h).2⟩} :=
  Classical.choose_spec h

def selectedSource (h : Applicable G) (w : SharpPWitness ea f) :=
  source G (selected G h).1 (selected G h).2
    (selected_spec G h).1 (selected_spec G h).2 w

theorem selectedWitnessCountingHard (h : Applicable G) :
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard
      (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
      (O.originalValue G) := by
  intro α ea f w
  exact ⟨(selectedSource G h w).reduction⟩

/-- Exact remaining region for this finite branch. This is not a claim that
all these residual signatures have ARS or that every non-ARS signature escapes. -/
theorem not_applicable_iff (heo : ∀i,Signature.CentralSupport (G i)) :
    ¬Applicable G ↔ ∀c : Choice s a,EOTract {⟨4,coefficient G c.1 c.2⟩} := by
  classical
  constructor
  · intro h c
    by_contra ht
    exact h ⟨c,heo c.1,ht⟩
  · intro h ⟨c,_,hc⟩
    exact hc (h c)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonARSPinningCaps
