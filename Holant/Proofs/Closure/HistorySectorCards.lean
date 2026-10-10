import Holant.Proofs.Closure.HistorySectorCardsAlgebra
import Holant.Proofs.Closure.ContinuationTransport
import Holant.Proofs.Algorithms.RingHomRealization
import Holant.Holographic

/-! Exact CURRENT raw keys at a fixed marked basis, including every optional
attachment, orientation and ordered port permutation. The sector card uses
the actual sector edge and the SAME original representatives and key. No
fresh X-native deck or newly chosen factorization is identified with it. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCards
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.OpenNetworkComposition
open HistorySectorCardsAlgebra
open scoped BigOperators
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapSignature)
end RH
variable {L : Type*} [Field L]

def mapBinary (phi : L →+* AlgebraicComplex) (B : Binary (K:=L)) : Mat :=
  fun a b => phi (B a b)

theorem map_X (phi : L →+* AlgebraicComplex) : mapBinary phi (X : Binary (K:=L)) =
    Signature.disequality := by
  funext a b
  cases a <;> cases b <;> simp [mapBinary,X,Signature.disequality]

theorem map_mul (phi : L →+* AlgebraicComplex) (B C : Binary (K:=L)) :
    mapBinary phi (B*C) = Kernel.mul (mapBinary phi B) (mapBinary phi C) := by
  funext a b
  simp [mapBinary,Matrix.mul_apply,Kernel.mul]

theorem map_splice {n : ℕ} (phi : L →+* AlgebraicComplex) (B : Binary (K:=L))
    (f : Signature L n) (i : Fin n) :
    RH.mapSignature phi (spliceTensor f (binarySignature B) i) =
      weightedSplice Signature.disequality (mapBinary phi B) (RH.mapSignature phi f) i := by
  rw [weightedSplice_native]
  funext x
  simp [RH.mapSignature,Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature,
    spliceTensor,binarySignature,mapBinary,Signature.disequality]

theorem map_contract {n : ℕ} (phi : L →+* AlgebraicComplex) (B : Binary (K:=L))
    (f : Signature L (n+2)) :
    RH.mapSignature phi (Signature.contract B f) =
      Signature.contract (mapBinary phi B) (RH.mapSignature phi f) := by
  funext x
  simp [RH.mapSignature,Holant.LocalDrafts.MainChain.RingHomRealization.mapSignature,
    Signature.contract,mapBinary]

def dressedAt {n : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (f : Signature AlgebraicComplex n)
    (delta : Fin n → Option (completeGroup F torsion × Bool)) (i : Fin n) :
    Signature AlgebraicComplex n :=
  match delta i with
  | none => f
  | some (j,reverse) => weightedSplice (sectorEdge U)
      (transport U (mapBinary phi (orientBinary reverse (actualRepresentative F torsion j)))) f i

def dressed {n : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (f : Signature AlgebraicComplex n)
    (delta : Fin n → Option (completeGroup F torsion × Bool)) : Signature AlgebraicComplex n :=
  (List.finRange n).foldl (fun g i => dressedAt phi U F torsion g delta i) f

theorem dressAt_transport {n : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L n)
    (delta : Fin n → Option (completeGroup F torsion × Bool)) (i : Fin n) :
    U.symm.action (RH.mapSignature phi (dressAt F torsion f delta i)) =
      dressedAt phi U F torsion (U.symm.action (RH.mapSignature phi f)) delta i := by
  cases hd : delta i with
  | none => simp [dressAt,dressedAt,hd]
  | some j =>
    simp only [dressAt,dressedAt,hd]
    rw [map_splice,atPort_conjugate]

theorem dressFold_transport {n : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F)
    (delta : Fin n → Option (completeGroup F torsion × Bool))
    (is : List (Fin n)) (f : Signature L n) :
    U.symm.action (RH.mapSignature phi (is.foldl (fun g i => dressAt F torsion g delta i) f)) =
      is.foldl (fun g i => dressedAt phi U F torsion g delta i)
        (U.symm.action (RH.mapSignature phi f)) := by
  induction is generalizing f with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldl_cons]
    rw [ih,dressAt_transport]

theorem dress_transport {n : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L n)
    (delta : Fin n → Option (completeGroup F torsion × Bool)) :
    U.symm.action (RH.mapSignature phi (dress F torsion f delta)) =
      dressed phi U F torsion (U.symm.action (RH.mapSignature phi f)) delta :=
  dressFold_transport phi U F torsion delta (List.finRange n) f

def card {m : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2))
    (key : RawCardKey m (completeGroup F torsion)) : Signature AlgebraicComplex m :=
  Signature.contract (Kernel.mul (Kernel.mul (sectorEdge U)
      (transport U (mapBinary phi (orientBinary key.2.2.2
        (actualRepresentative F torsion key.2.2.1))))) (sectorEdge U))
    (Tensor.reindex key.2.1.symm
      (dressed phi U F torsion (U.symm.action (RH.mapSignature phi f)) key.1))

/-- Every original literal key, with its EXACT residual port order and all
scalar factors of both the transformed binary and changed edge retained. -/
theorem card_transport {m : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2))
    (key : RawCardKey m (completeGroup F torsion)) :
    U.symm.action (RH.mapSignature phi (rawCard F torsion f key)) =
      card phi U F torsion f key := by
  unfold rawCard
  rw [map_contract,contract_transport]
  have hr : RH.mapSignature phi (Tensor.reindex key.2.1.symm (dress F torsion f key.1)) =
      Tensor.reindex key.2.1.symm (RH.mapSignature phi (dress F torsion f key.1)) := rfl
  rw [hr,reindex_transport,dress_transport,map_mul,map_mul,map_X,
    Holant.Marked.SupportAtlas.effective_transport]
  rfl

theorem action_map_scalar {n : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (c : L) (f : Signature L n) :
    U.symm.action (RH.mapSignature phi (c • f)) =
      phi c • U.symm.action (RH.mapSignature phi f) := by
  have he : RH.mapSignature phi (c • f) = phi c • RH.mapSignature phi f := by
    funext x
    exact phi.map_mul c (f x)
  rw [he]
  exact ClosureFactorTreeAction.coordinateAction_scale _ _ _

/-- A separately recorded nonzero source-field representative multiplier is
mapped literally; it is never silently replaced by an algebraic normalization. -/
theorem card_scalar {m : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2))
    (key : RawCardKey m (completeGroup F torsion)) (g : Signature L m)
    (c : L) (hc : c ≠ 0) (he : rawCard F torsion f key = c • g) :
    card phi U F torsion f key = phi c • U.symm.action (RH.mapSignature phi g) ∧ phi c ≠ 0 := by
  refine ⟨?_,(map_ne_zero phi).mpr hc⟩
  rw [←card_transport,he,action_map_scalar]

theorem card_zero_iff {m : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2))
    (key : RawCardKey m (completeGroup F torsion)) :
    card phi U F torsion f key = 0 ↔ rawCard F torsion f key = 0 := by
  rw [←card_transport]
  constructor
  · intro hz
    have he := congrArg U.action hz
    rw [U.action_symm_action,ClosureFactorTreeAction.action_zero] at he
    funext x
    apply phi.injective
    exact (congrFun he x).trans phi.map_zero.symm
  · intro hz
    rw [hz]
    have he : RH.mapSignature phi (0 : Signature L m) = 0 := by funext x; exact phi.map_zero
    rw [he,ClosureFactorTreeAction.action_zero]

def deck {m : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2)) :
    Set (Signature AlgebraicComplex m) := {0} ∪ Set.range (card phi U F torsion f)

/-- Exact image of the entire CURRENT raw deck, including its standalone
zero sentinel. The image uses the original raw keys rather than sector choices. -/
theorem deck_exact {m : ℕ} (phi : L →+* AlgebraicComplex) (U : InvertibleKernel)
    (F : SignatureFamily L) (torsion : ResidualTorsion F) (f : Signature L (m+2)) :
    deck phi U F torsion f = (fun g => U.symm.action (RH.mapSignature phi g)) '' rawDeck F torsion f := by
  have hz : U.symm.action (RH.mapSignature phi (0 : Signature L m)) = 0 := by
    have he : RH.mapSignature phi (0 : Signature L m) = 0 := by funext x; exact phi.map_zero
    rw [he,ClosureFactorTreeAction.action_zero]
  ext g
  constructor
  · rintro (rfl | ⟨key,rfl⟩)
    · exact ⟨0,Or.inl rfl,hz⟩
    · exact ⟨rawCard F torsion f key,Or.inr ⟨key,rfl⟩,card_transport phi U F torsion f key⟩
  · rintro ⟨h,(rfl | ⟨key,rfl⟩),rfl⟩
    · exact Or.inl hz
    · exact Or.inr ⟨key,(card_transport phi U F torsion f key).symm⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorCards
end
