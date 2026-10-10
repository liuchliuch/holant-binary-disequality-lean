import Holant.Proofs.Closure.ClosureSourceRowsDeck

/-! Actual ordered cards for an arbitrary original-field current binary.
Coverage restores its exact original-field unit relative to a selected full
deck representative. Direct graphs and charged programmes realize the original
card, never a unit-normalized table inferred only from projective equality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.OpenNetworkComposition

variable {L : Type*} [Field L]

def originalOrderedCard (q : Signature L 4) (e : Equiv.Perm (Fin 4))
    (B : Binary (K:=L)) : Signature L 2 :=
  Signature.contract (X * B * X) (Tensor.reindex e.symm q)

theorem originalOrderedCard_scale (q : Signature L 4) (e : Equiv.Perm (Fin 4))
    (B : Binary (K:=L)) (c : L) :
    originalOrderedCard q e (c • B) = c • originalOrderedCard q e B := by
  unfold originalOrderedCard
  rw [Matrix.mul_smul,Matrix.smul_mul]
  simpa only [one_smul,mul_one] using
    ContinuationTransport.contract_smul (X * B * X) (Tensor.reindex e.symm q) c 1

theorem actualCard_raw_scalar (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (q : Signature L 4) (e : Equiv.Perm (Fin 4)) (B : Binary (K:=L))
    (hB : ActualNonsingular F B) :
    ∃ j : completeGroup F torsion, ∃ c : L, c ≠ 0 ∧
      originalOrderedCard q e B = c • rawCard F torsion q (orderedKey F torsion e j) := by
  obtain ⟨j,c,hc,he⟩ := actual_binary_eq_representative F torsion B hB
  refine ⟨j,c,hc,?_⟩
  rw [he,originalOrderedCard_scale,rawCard_ordered]
  rfl

/-- Genuine native-X closure of an actual q and actual B over the same F.
Literal I makes ordinary self-contraction exact, with no discarded half. -/
theorem originalOrderedCard_realizes (F : SignatureFamily L) (hI : RetainsIdentity F)
    (q : Signature L 4) (hq : Gadget.Realizes F .disequality q)
    (e : Equiv.Perm (Fin 4)) (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    Gadget.Realizes F .disequality (originalOrderedCard q e B) := by
  have hr := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality q hq e
  have hs := realizes_splice F _ _ hr hB.1 (1 : Fin 4)
  have hc := realizes_contract_exact_of_identity F hI _ hs
  simpa only [close_splice_table,originalOrderedCard] using hc

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4)

/-- The source theorem's bilinear card is exactly the embedded original card. -/
theorem sourceCard_actual (e : Equiv.Perm (Fin 4)) (B : Binary (K:=OI.K G)) :
    Holant.Marked.SupportAtlas.physicalCard (RingHomRealization.mapSignature (embedding G) q) e
      (B.map (embedding G)) =
        (binaryMatrix (originalOrderedCard q e B)).map (embedding G) := by
  funext u v
  have hwords (a b : Bool) :
      (Fin.cons a (Fin.cons b (![u,v] : Fin 2 → Bool)) : Fin 4 → Bool) = ![a,b,u,v] := by
    funext i
    fin_cases i <;> rfl
  simp only [Holant.Marked.SupportAtlas.physicalCard,Holant.Marked.SupportAtlas.contract0,
    Holant.Marked.SupportAtlas.reorder,RingHomRealization.mapSignature,binaryMatrix,
    originalOrderedCard,Matrix.map_apply,Signature.contract,Tensor.reindex,map_sum,map_mul,hwords]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Kernel.disequality_sandwich]
  congr 1
  exact congrArg (embedding G) (nativePair_apply B a b).symm

/-- Every physical actual card is a nonzero mapped ORIGINAL-field scalar
times a literal no-dressing raw key; its zero branch is thereby preserved. -/
theorem sourceCard_raw_scalar (e : Equiv.Perm (Fin 4)) (B : Binary (K:=OI.K G))
    (hB : ActualNonsingular P.family B) :
    ∃ j : completeGroup P.family torsion, ∃ c : OI.K G, c ≠ 0 ∧
      Holant.Marked.SupportAtlas.physicalCard (RingHomRealization.mapSignature (embedding G) q) e
        (B.map (embedding G)) =
          (embedding G c) • (binaryMatrix
            (rawCard P.family torsion q (orderedKey P.family torsion e j))).map (embedding G) := by
  obtain ⟨j,c,hc,he⟩ := actualCard_raw_scalar P.family torsion q e B hB
  refine ⟨j,c,hc,?_⟩
  rw [sourceCard_actual,he]
  funext a b
  exact map_mul (embedding G) c
    (rawCard P.family torsion q (orderedKey P.family torsion e j) ![a,b])

variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)

def actualCardDirect (e : Equiv.Perm (Fin 4)) (B : Binary (K:=OI.K G))
    (hB : ActualNonsingular P.family B) : DeckDirect P.family (originalOrderedCard q e B) :=
  DeckDirect.ofRealizes (P.retainsIdentity G) (originalOrderedCard_realizes P.family
    (P.retainsIdentity G) q (Gadget.realizes_of_mem P.family .disequality q
      (by simpa only [hcore] using core.retained)) e B hB)

def actualCardAccess (e : Equiv.Perm (Fin 4)) (B : Binary (K:=OI.K G))
    (hB : ActualNonsingular P.family B) : CurrentSignatureAccess G P ⟨2,originalOrderedCard q e B⟩ :=
  currentSignatureAccess G P _ (actualCardDirect G P q core hcore e B hB).realizes

@[simp] theorem actualCardAccess_same_controlled (e : Equiv.Perm (Fin 4))
    (B : Binary (K:=OI.K G)) (hB : ActualNonsingular P.family B) :
    (actualCardAccess G P q core hcore e B hB).toOriginal.controlled =
      RetainedBranch.controlledToOriginal G P _
        (actualCardAccess G P q core hcore e B hB).power := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
