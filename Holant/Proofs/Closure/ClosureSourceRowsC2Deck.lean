import Holant.Proofs.Closure.ClosureSourceRowsC2Group
import Holant.Proofs.Algorithms.PrimalityInterfaces

/-! A closed C2 q4 source boundary from the real order-two current group and
the actual stable current raw deck. Literal representatives, retainedness,
all ordered source cards, primality and the at-most-two-copy boundary are
constructed; a SourceDeck or complete-group classifier is never an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
open Holant Holant.Algebraic Holant.Tractable Holant.Certificates
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain

def pairPermutation (i : Fin 3) (side order : Bool) : Equiv.Perm (Fin 4) :=
  (if order then Equiv.swap 2 3 else Equiv.refl _).trans
    ((if side then (Equiv.swap 0 2).trans (Equiv.swap 1 3) else Equiv.refl _).trans
      (if i=0 then Equiv.refl _ else if i=1 then Equiv.swap 1 2
        else (Equiv.swap 1 2).trans (Equiv.swap 2 3)))

/-- The Fin3/side/residual-order source convention is the same ordered
24-permutation physical card used in the current literal raw catalogue. -/
theorem pairPermutation_card (q : Signature AlgebraicComplex 4) (i : Fin 3)
    (side order : Bool) (B : Kernel AlgebraicComplex) :
    Holant.Marked.SupportAtlas.physicalCard q (pairPermutation i side order) B =
      Holant.Projective.CyclicQuaternary.Physical.orderedPhysicalCard q i side order B := by
  funext u v
  unfold Holant.Marked.SupportAtlas.physicalCard Holant.Marked.SupportAtlas.contract0
    Holant.Marked.SupportAtlas.reorder Holant.Marked.SupportAtlas.permuteWord
    Holant.Projective.CyclicQuaternary.Physical.orderedPhysicalCard
    Holant.Projective.CyclicQuaternary.Physical.physicalCard
    Holant.Projective.CyclicQuaternary.Physical.contractKernel
  cases order <;> simp only [Bool.false_eq_true,ite_false,ite_true,Kernel.transpose]
  all_goals
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    apply congrArg q
    funext k
    fin_cases i <;> cases side <;> fin_cases k <;>
      simp [pairPermutation,Holant.Projective.CyclicQuaternary.join,Equiv.swap_apply_def]

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4)

theorem originalC2Binary_map (p : Bool) :
    (originalC2Binary (L:=OI.K G) p).map (embedding G) = EqualityQuaternary.C2.binary p := by
  funext a b
  cases p <;> cases a <;> cases b <;> simp [originalC2Binary,X,Matrix.map_apply,EqualityQuaternary.C2.binary,
    Matrix.one_apply,Signature.equality,Signature.disequality]

theorem originalC2Binary_actual (p : Bool) : ActualNonsingular P.family
    (originalC2Binary (L:=OI.K G) p) := by
  cases p
  · exact identity_actual P.family (P.retainsIdentity G)
  · exact nativeX_actual P.family

variable (core : MinimumCore P.family) (hcore : core.signature = ⟨4,q⟩)
variable (stableDeck : ∀ g ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) g)
variable (cardTwo : Nat.card (completeGroup P.family torsion) = 2)
include core hcore stableDeck cardTwo

theorem sourceCard_c2Line (e : Equiv.Perm (Fin 4)) (B : Binary (K:=OI.K G))
    (hB : ActualNonsingular P.family B) :
    Holant.Marked.SupportAtlas.physicalCard (RingHomRealization.mapSignature (embedding G) q) e
      (B.map (embedding G)) = 0 ∨
    EqualityQuaternary.C2.ActualLine (c2Representatives G P torsion q core hcore (by norm_num))
      (Holant.Marked.SupportAtlas.physicalCard (RingHomRealization.mapSignature (embedding G) q) e
        (B.map (embedding G))) := by
  rcases actualCard_actual_or_zero G P torsion q stableDeck core hcore e B hB with hz | ha
  · left
    rw [sourceCard_actual,hz]
    funext a b
    simp [binaryMatrix,Matrix.map_apply]
  · obtain ⟨p,c,hc,he⟩ := c2_actual_binary P.family torsion (P.retainsIdentity G) cardTwo _ ha
    refine Or.inr ⟨p,embedding G c,(map_ne_zero (embedding G)).mpr hc,?_⟩
    rw [sourceCard_actual,he,Matrix.map_smul' (embedding G) c _ (embedding G).map_mul,
      originalC2Binary_map]
    rfl

/-- The exact C2 SourceDeck is derived, not supplied. Zero samples and all
original deleted/residual orders are covered by the current stable raw deck. -/
theorem c2_sourceDeck : EqualityQuaternary.SourceDeck .c2
    (c2Representatives G P torsion q core hcore (by norm_num))
    (RingHomRealization.mapSignature (embedding G) q) := by
  intro i side order p
  have h := sourceCard_c2Line G P torsion q core hcore stableDeck cardTwo
    (pairPermutation i side order) (originalC2Binary (L:=OI.K G) p)
    (originalC2Binary_actual G P p)
  rw [originalC2Binary_map,pairPermutation_card] at h
  exact h

omit stableDeck cardTwo in
theorem core_ambient_prime : EqualityQuaternary.TensorPrime
    (RingHomRealization.mapSignature (embedding G) q) := by
  apply (PrimalityInterfaces.retained_equality_prime _).mp
  apply (prime_mapSignature_iff (embedding G) (⟨4,q⟩ : AnySignature (OI.K G))).mpr
  simpa only [hcore] using core.prime

omit stableDeck cardTwo in
theorem core_ambient_retained :
    (⟨4,RingHomRealization.mapSignature (embedding G) q⟩ : AnySignature AlgebraicComplex) ∈
      ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num)) := by
  refine ⟨⟨4,q⟩,?_,rfl⟩
  rw [ProgrammeRetained.palette_family]
  exact fullRetainedDeck_retains P.family torsion q (by simpa only [hcore] using core.retained)

/-- Source A.8 in the actual order-two branch, with the real augmented
palette and all its original-G programmes already internally constructed. -/
theorem c2_source_interface :
    EqualityQuaternary.BoundaryCertificate
      (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num)))
      (RingHomRealization.mapSignature (embedding G) q) (EqualityQuaternary.SourceGroup .c2) ∧
    EqualityQuaternary.SourceDetail
      (ambientFamily G (retainedPalette G P torsion q core hcore (by norm_num)))
      (RingHomRealization.mapSignature (embedding G) q) .c2
      (c2Representatives G P torsion q core hcore (by norm_num)) :=
  EqualityQuaternary.source_equality_accessible_quaternary_interface _ .c2 trivial
    (c2Representatives G P torsion q core hcore (by norm_num))
    (c2_retained G P torsion q core hcore (by norm_num)) _
    (core_ambient_prime G P q core hcore)
    (core_ambient_retained G P torsion q core hcore)
    (identity_ambient_retained G P torsion q core hcore (by norm_num))
    (c2_sourceDeck G P torsion q core hcore stableDeck cardTwo)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSourceRows
