import Holant.Proofs.Reductions.FrozenFactorNormalization.NormalizedTree


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FrozenFactorNormalization.Palette
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {L E : Type} [Field L] [Field E] (φ : L →+* E)
variable {m t : ℕ} (P : Fin m → AnySignature L) (C : Fin t → AnySignature E)
variable (U : ∀ i, KeyLift φ (C i))

def signature (i : Fin (m+t)) : AnySignature L :=
  if hi : i.val < m then P ⟨i.val,hi⟩ else lifted φ (U ⟨i.val-m,by omega⟩)
def family : SignatureFamily L := Set.range (signature φ P C U)
def rootIndex (i : Fin m) : Fin (m+t) := ⟨i.val,by omega⟩
def keyIndex (i : Fin t) : Fin (m+t) := ⟨m+i.val,by omega⟩
@[simp] theorem signature_root (i : Fin m) : signature φ P C U (rootIndex (t:=t) i) = P i := by
  simp [signature,rootIndex,i.isLt]
@[simp] theorem signature_key (i : Fin t) : signature φ P C U (keyIndex (m:=m) i) = lifted φ (U i) := by
  unfold signature keyIndex
  dsimp only
  rw [dif_neg (by omega)]
  have he : (⟨m+i.val-m,by omega⟩ : Fin t) = i := Fin.ext (by simp)
  rw [he]
theorem family_exact : family φ P C U = Set.range P ∪ Set.range (fun i => lifted φ (U i)) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val < m
    · exact Or.inl ⟨⟨i.val,hi⟩,by simp [signature,hi]⟩
    · exact Or.inr ⟨⟨i.val-m,by omega⟩,by simp [signature,hi]⟩
  · rintro (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · exact ⟨rootIndex i,signature_root φ P C U i⟩
    · exact ⟨keyIndex i,signature_key φ P C U i⟩
theorem finite_family : (family φ P C U).Finite := Set.finite_range _
theorem retains_root (i : Fin m) : P i ∈ family φ P C U := ⟨rootIndex i,signature_root φ P C U i⟩
theorem retains_key (i : Fin t) : lifted φ (U i) ∈ family φ P C U := ⟨keyIndex i,signature_key φ P C U i⟩

variable (hn : ∀ i, (C i).2 ≠ 0)
variable (ρ : Fin m → Fin t) (hP : ∀ i, RH.mapAny φ (P i) = C (ρ i))
def target (i : Fin (m+t)) : Fin t :=
  if hi : i.val < m then ρ ⟨i.val,hi⟩ else ⟨i.val-m,by omega⟩
def pivot (i : Fin t) : E := (C i).2 (firstWord (C i).2 (hn i))
def correction (i : Fin (m+t)) : E := if hi : i.val < m then 1 else (pivot C hn ⟨i.val-m,by omega⟩)⁻¹
theorem pivot_ne (i : Fin t) : pivot C hn i ≠ 0 := firstWord_nonzero _ _

include hP in
theorem projective (i : Fin (m+t)) : RH.mapAny φ (signature φ P C U i) =
    ⟨(C (target ρ i)).1,correction C hn i • (C (target ρ i)).2⟩ := by
  by_cases hi : i.val < m
  · have ht : target ρ i = ρ ⟨i.val,hi⟩ := by unfold target; rw [dif_pos hi]
    rw [ht]
    simp only [signature,correction,dif_pos hi,if_pos hi,one_smul]
    exact hP _
  · have ht : target ρ i = ⟨i.val-m,by omega⟩ := by unfold target; rw [dif_neg hi]
    rw [ht]
    simpa only [signature,correction,dif_neg hi,if_neg hi,keyAny,pivot,canonicalKey_of_ne_zero _ (hn _)] using
      lifted_map φ (U ⟨i.val-m,by omega⟩)

include hn ρ hP in
theorem nonzero (i : Fin (m+t)) : (signature φ P C U i).2 ≠ 0 := by
  intro hz
  have he := projective φ P C U hn ρ hP i
  have ht : (correction C hn i) ≠ 0 := by
    by_cases hi : i.val < m <;> simp [correction,hi,pivot_ne]
  have hm : RH.mapAny φ (signature φ P C U i) = ⟨(signature φ P C U i).1,0⟩ := by
    simp [RH.mapAny,hz,RH.mapSignature]
    funext x
    exact map_zero φ
  rw [hm] at he
  have zero_of_pair {n k} {f : Signature E k} (h : (⟨n,0⟩ : AnySignature E)=⟨k,f⟩) : f=0 := by
    cases h
    rfl
  have hh := zero_of_pair he
  apply hn (target ρ i)
  funext x
  exact (mul_eq_zero.mp (congrFun hh x)).resolve_left ht

variable (T : ∀ i, FactorTree (C i))
variable (hT : ∀ i v, v ∈ (T i).leaves → v ∈ Set.range C)

include hT in
theorem normalized_leaves (i : Fin t) :
    ∀ u ∈ (normalizedTree φ (T i) (hn i) (U i)).leaves, u ∈ family φ P C U := by
  intro u hu
  obtain ⟨v,hv,he⟩ := normalizedTree_leaves φ (T i) (hn i) (U i) u hu
  obtain ⟨j,rfl⟩ := hT i v hv
  have eq : u = lifted φ (U j) := mapAny_injective φ (he.trans (lifted_map φ (U j)).symm)
  rw [eq]
  exact retains_key φ P C U j

include hn ρ hP T hT in
/-- This is the manuscript's literal FactorSaturated predicate. The new
split units belong to L; unnormalized old child scalars need not do so. -/
theorem saturated : FactorSaturated (family φ P C U) := by
  intro f hf _
  rw [family_exact] at hf
  rcases hf with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · have hp : (P i).2 ≠ 0 := by
      intro hz
      have hm : (RH.mapAny φ (P i)).2 ≠ 0 := by rw [hP i]; exact hn (ρ i)
      exact hm (by funext x; simp [RH.mapAny,RH.mapSignature,hz])
    let c : Lˣ := Units.mk0 ((P i).2 (firstWord (P i).2 hp)) (firstWord_nonzero _ hp)
    have hu : lifted φ (U (ρ i)) = ⟨(P i).1,canonicalKey (P i).2⟩ := by
      apply mapAny_injective φ
      rw [lifted_map,←hP i]
      exact (congrArg (fun t => (⟨(P i).1,t⟩ : AnySignature E)) (key_map φ (P i).2)).symm
    have hr : scaled c (lifted φ (U (ρ i))) = P i := by
      rw [hu]
      exact congrArg (fun t => (⟨(P i).1,t⟩ : AnySignature L)) (recover_from_key (P i).2 hp).symm
    let tree := scaleTree (normalizedTree φ (T (ρ i)) (hn (ρ i)) (U (ρ i))) c
    have ht : ∃ t : FactorTree (scaled c (lifted φ (U (ρ i)))),
        ∀ u ∈ t.leaves, u ∈ family φ P C U := by
      refine ⟨tree,?_⟩
      intro u hu'
      rcases scaleTree_leaves _ c u hu' with he | he
      · rw [he,hr]
        exact retains_root φ P C U i
      · exact normalized_leaves φ P C U hn T hT (ρ i) u he
    exact (congrArg (fun f : AnySignature L => ∃ t : FactorTree f,
      ∀ u ∈ t.leaves, u ∈ family φ P C U) hr).mp ht
  · exact ⟨normalizedTree φ (T i) (hn i) (U i),normalized_leaves φ P C U hn T hT i⟩

end Holant.LocalDrafts.Hardness.FrozenFactorNormalization.Palette
