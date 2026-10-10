import Holant.Proofs.FiniteGroups.Stabilization.MatchingStability

/-! RECONSTRUCTED AFTER WORKSPACE REPLACEMENT; fresh kernel verification is
required. Same-group actual representative changes keep explicit original-field
nonzero scalars and transport the CURRENT regenerated raw deck. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ContinuationTransport
open Holant Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.OpenNetworkComposition
variable {L : Type*} [Field L]

structure RepresentativeChange (F : SignatureFamily L) (hF : ResidualTorsion F)
    (G : SignatureFamily L) (hG : ResidualTorsion G) where
  label : completeGroup G hG → completeGroup F hF
  scale : completeGroup G hG → L
  scale_nonzero : ∀ q, scale q ≠ 0
  literal : ∀ q, actualRepresentative G hG q = scale q • actualRepresentative F hF (label q)

def representativeChange {F G : SignatureFamily L} (hFG : F ⊆ G)
    (hF : ResidualTorsion F) (hG : ResidualTorsion G)
    (he : completeGroup G hG = completeGroup F hF) : RepresentativeChange F hF G hG := by
  classical
  choose label scale hn hl using fun q : completeGroup G hG =>
    (frozen_representatives_cover_retained hFG hF hG he).2 _
      (actualRepresentative_actual G hG q)
  exact ⟨label,scale,hn,hl⟩

theorem orientBinary_smul (reverse : Bool) (B : Binary (K:=L)) (c : L) :
    orientBinary reverse (c • B) = c • orientBinary reverse B := by
  cases reverse <;> simp [orientBinary,Matrix.transpose_smul]

theorem binarySignature_smul (B : Binary (K:=L)) (c : L) :
    binarySignature (c • B) = c • binarySignature B := rfl

theorem splice_smul {n : ℕ} (f : Signature L n) (B : Signature L 2)
    (i : Fin n) (c d : L) :
    spliceTensor (c • f) (d • B) i = (c*d) • spliceTensor f B i := by
  funext x
  change (∑ a : Bool, ∑ b : Bool,
    (c * f (Function.update x i a)) * (d * B (![x i,b])) * Signature.disequality a b) =
      (c*d) * ∑ a : Bool, ∑ b : Bool,
        f (Function.update x i a) * B (![x i,b]) * Signature.disequality a b
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem reindex_smul {n : ℕ} (e : Equiv.Perm (Fin n)) (f : Signature L n) (c : L) :
    Tensor.reindex e (c • f) = c • Tensor.reindex e f := rfl

theorem contract_smul {m : ℕ} (C : Binary (K:=L)) (f : Signature L (m+2)) (c d : L) :
    Signature.contract (c • C) (d • f) = (c*d) • Signature.contract C f := by
  funext x
  change (∑ a : Bool, ∑ b : Bool,
    (c * C a b) * (d * f (Fin.cons a (Fin.cons b x)))) =
      (c*d) * ∑ a : Bool, ∑ b : Bool, C a b * f (Fin.cons a (Fin.cons b x))
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

namespace RepresentativeChange
variable {F G : SignatureFamily L} {hF : ResidualTorsion F} {hG : ResidualTorsion G}
variable (T : RepresentativeChange F hF G hG)

theorem label_class (q : completeGroup G hG) : (T.label q).val = q.val := by
  apply pglToProjectiveClass_injective
  rw [← actualRepresentative_class F hF (T.label q),← actualRepresentative_class G hG q,
    T.literal]
  have hs : transfer (T.scale q • actualRepresentative F hF (T.label q)) =
      T.scale q • transfer (actualRepresentative F hF (T.label q)) := by
    simp only [transfer,Matrix.smul_mul]
  rw [hs,projectiveClass_smul _ (T.scale_nonzero q)]

def reverse (he : completeGroup G hG = completeGroup F hF) : RepresentativeChange G hG F hF where
  label q := ⟨q.val,he.symm ▸ q.property⟩
  scale q := (T.scale ⟨q.val,he.symm ▸ q.property⟩)⁻¹
  scale_nonzero q := inv_ne_zero (T.scale_nonzero _)
  literal q := by
    let r : completeGroup G hG := ⟨q.val,he.symm ▸ q.property⟩
    have hl : T.label r = q := Subtype.ext (T.label_class r)
    rw [T.literal r,hl,smul_smul,inv_mul_cancel₀ (T.scale_nonzero r),one_smul]

def optionLabel (q : Option (completeGroup G hG × Bool)) :
    Option (completeGroup F hF × Bool) := q.map (fun p => (T.label p.1,p.2))

def optionScale : Option (completeGroup G hG × Bool) → L
  | none => 1
  | some q => T.scale q.1

theorem optionScale_nonzero (q : Option (completeGroup G hG × Bool)) : T.optionScale q ≠ 0 := by
  cases q with
  | none => exact one_ne_zero
  | some q => exact T.scale_nonzero q.1

def dressing {n : ℕ} (δ : Fin n → Option (completeGroup G hG × Bool)) :
    Fin n → Option (completeGroup F hF × Bool) :=
  fun i => (δ i).map (fun p => (T.label p.1,p.2))

def key {m : ℕ} (k : RawCardKey m (completeGroup G hG)) : RawCardKey m (completeGroup F hF) :=
  (T.dressing k.1, k.2.1, T.label k.2.2.1, k.2.2.2)

abbrev rawKey {m : ℕ} (k : RawCardKey m (completeGroup G hG)) := T.key k
abbrev mapKey {m : ℕ} (k : RawCardKey m (completeGroup G hG)) := T.key k

def listScale {n : ℕ} (δ : Fin n → Option (completeGroup G hG × Bool)) : List (Fin n) → L
  | [] => 1
  | i::is => T.optionScale (δ i) * listScale δ is

theorem listScale_nonzero {n : ℕ} (δ : Fin n → Option (completeGroup G hG × Bool))
    (is : List (Fin n)) : T.listScale δ is ≠ 0 := by
  induction is with
  | nil => exact one_ne_zero
  | cons i is ih => exact mul_ne_zero (T.optionScale_nonzero _) ih

def dressScale {n : ℕ} (δ : Fin n → Option (completeGroup G hG × Bool)) : L :=
  T.listScale δ (List.finRange n)

def cardScale {m : ℕ} (k : RawCardKey m (completeGroup G hG)) : L :=
  T.scale k.2.2.1 * T.dressScale k.1

abbrev scalar {m : ℕ} (k : RawCardKey m (completeGroup G hG)) := T.cardScale k

theorem cardScale_nonzero {m : ℕ} (k : RawCardKey m (completeGroup G hG)) : T.cardScale k ≠ 0 :=
  mul_ne_zero (T.scale_nonzero _) (T.listScale_nonzero _ _)

theorem oriented (q : completeGroup G hG) (reverse : Bool) :
    orientBinary reverse (actualRepresentative G hG q) =
      T.scale q • orientBinary reverse (actualRepresentative F hF (T.label q)) := by
  rw [T.literal,orientBinary_smul]

theorem dressAt_transport {n : ℕ} (g : Signature L n)
    (δ : Fin n → Option (completeGroup G hG × Bool)) (i : Fin n) (c : L) :
    dressAt G hG (c • g) δ i = (c*T.optionScale (δ i)) •
      dressAt F hF g (fun j => T.optionLabel (δ j)) i := by
  cases h : δ i with
  | none => simp [dressAt,h,optionScale,optionLabel]
  | some q =>
      simp only [dressAt,h,optionLabel,Option.map_some,optionScale]
      rw [T.oriented,binarySignature_smul,splice_smul]

theorem dressFold_transport {n : ℕ} (is : List (Fin n)) (g : Signature L n)
    (δ : Fin n → Option (completeGroup G hG × Bool)) (c : L) :
    is.foldl (fun f i => dressAt G hG f δ i) (c • g) =
      (c*T.listScale δ is) • is.foldl
        (fun f i => dressAt F hF f (fun j => T.optionLabel (δ j)) i) g := by
  induction is generalizing g c with
  | nil => simp [listScale]
  | cons i is ih =>
      simp only [List.foldl_cons,listScale]
      rw [T.dressAt_transport,ih,mul_assoc]

theorem dress_transport {n : ℕ} (f : Signature L n)
    (δ : Fin n → Option (completeGroup G hG × Bool)) :
    dress G hG f δ = T.dressScale δ • dress F hF f (fun i => T.optionLabel (δ i)) := by
  simpa only [dress,dressScale,one_smul,one_mul] using T.dressFold_transport (List.finRange n) f δ 1

theorem rawCard_transport {m : ℕ} (f : Signature L (m+2))
    (k : RawCardKey m (completeGroup G hG)) :
    rawCard G hG f k = T.cardScale k • rawCard F hF f (T.key k) := by
  unfold rawCard
  rw [T.oriented,Matrix.mul_smul,Matrix.smul_mul,T.dress_transport,reindex_smul,contract_smul]
  rfl

end RepresentativeChange

/-- Full original-field scalar receipt for a current literal card. -/
theorem rawCard_transport {F G : SignatureFamily L} {hF : ResidualTorsion F}
    {hG : ResidualTorsion G} (T : RepresentativeChange F hF G hG) {m : ℕ}
    (f : Signature L (m+2)) (k : RawCardKey m (completeGroup G hG)) :
    ∃ c : L, c ≠ 0 ∧ rawCard G hG f k = c • rawCard F hF f (T.key k) :=
  ⟨T.cardScale k,T.cardScale_nonzero k,T.rawCard_transport f k⟩

theorem matching_smul {P : Type*} {H : Set (Binary (K:=L))} {f : Tensor L P}
    (hf : MatchingOrZero H f) (c : L) (hc : c ≠ 0) : MatchingOrZero H (c • f) := by
  rcases hf with hz | ⟨M,hM,hs,rfl⟩
  · exact Or.inl (by rw [hz,smul_zero])
  · let N : Presentation L P := { M with scalar := c*M.scalar }
    refine Or.inr ⟨N,hM,mul_ne_zero hc hs,?_⟩
    funext x
    simp [N,Presentation.tensor,productValue,mul_assoc]

theorem regenerated_matching {F G : SignatureFamily L} {m : ℕ}
    (hFG : F ⊆ G) (hF : ResidualTorsion F) (hG : ResidualTorsion G)
    (he : completeGroup G hG = completeGroup F hF) (f : Signature L (m+2))
    (hmatch : ∀ g ∈ rawDeck F hF f, MatchingOrZero (actualTransfers G) g) :
    ∀ g ∈ rawDeck G hG f, MatchingOrZero (actualTransfers G) g := by
  let T := representativeChange hFG hF hG he
  intro g hg
  rcases hg with hz | ⟨k,rfl⟩
  · exact Or.inl hz
  · rw [T.rawCard_transport]
    exact matching_smul (hmatch _ (Or.inr ⟨T.key k,rfl⟩)) _ (T.cardScale_nonzero k)

theorem fullRetainedDeck_regenerated_matching [NumberField L] {m : ℕ} (hm : 2 ≤ m)
    (F : SignatureFamily L) (hF : ResidualTorsion F) (f : Signature L (m+2))
    (core : MinimumCore (fullRetainedDeck F hF f)) (hmin : m+2 ≤ core.signature.1)
    (hG : ResidualTorsion (fullRetainedDeck F hF f))
    (he : completeGroup (fullRetainedDeck F hF f) hG = completeGroup F hF)
    (hu : ¬ RetainedUnary (fullRetainedDeck F hF f)) :
    ∀ g ∈ rawDeck (fullRetainedDeck F hF f) hG f,
      MatchingOrZero (actualTransfers (fullRetainedDeck F hF f)) g :=
  regenerated_matching (fullRetainedDeck_retains F hF f) hF hG he f
    (fullRetainedDeck_matching hm F hF f core hmin hu)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ContinuationTransport
end
