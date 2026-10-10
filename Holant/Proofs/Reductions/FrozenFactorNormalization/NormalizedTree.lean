import Holant.Proofs.Reductions.FrozenFactorNormalization.SameTree


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {K L E : Type*} [Field K] [Field L] [Field E]

def scaled (c : Kˣ) (f : AnySignature K) : AnySignature K := ⟨f.1,(c : K) • f.2⟩
def scaleSplit {f a b : AnySignature K} (S : ProperSplit f a b) (c : Kˣ) :
    ProperSplit (scaled c f) a b where
  left_pos := S.left_pos
  right_pos := S.right_pos
  ports := S.ports
  scale := c*S.scale
  equation := by funext x; simp [scaled,S.equation,mul_assoc,Pi.smul_apply,smul_eq_mul]

theorem prime_scaled (c : Kˣ) {f : AnySignature K} (h : Prime f) : Prime (scaled c f) := by
  refine ⟨?_,?_⟩
  · intro hz
    apply h.1
    funext x
    exact (mul_eq_zero.mp (congrFun hz x)).resolve_left c.ne_zero
  · rintro ⟨a,b,⟨S⟩⟩
    have T := scaleSplit S c⁻¹
    have he : scaled c⁻¹ (scaled c f) = f := by
      cases f
      unfold scaled
      congr 1
      funext x
      simp [scaled,Pi.smul_apply,smul_eq_mul,← mul_assoc,c.ne_zero]
    rw [he] at T
    exact h.2 ⟨a,b,⟨T⟩⟩

def scaleTree {f : AnySignature K} (t : FactorTree f) (c : Kˣ) : FactorTree (scaled c f) :=
  match t with
  | .leaf _ p => .leaf _ (prime_scaled c p)
  | .split S l r => .split (scaleSplit S c) l r

theorem scaleTree_leaves {f : AnySignature K} (t : FactorTree f) (c : Kˣ)
    (u : AnySignature K) (hu : u ∈ (scaleTree t c).leaves) :
    u = scaled c f ∨ u ∈ t.leaves := by
  cases t with
  | leaf f p => exact Or.inl (Multiset.mem_singleton.mp hu)
  | split S l r => exact Or.inr hu

def keyAny (f : AnySignature E) : AnySignature E := ⟨f.1,canonicalKey f.2⟩
theorem prime_key {f : AnySignature E} (h : Prime f) : Prime (keyAny f) := by
  simpa [keyAny,scaled,canonicalKey_of_ne_zero f.2 h.1] using
    prime_scaled (Units.mk0 (f.2 (firstWord f.2 h.1))⁻¹
      (inv_ne_zero (firstWord_nonzero f.2 h.1))) h

variable (φ : L →+* E)
def lifted {f : AnySignature E} (U : KeyLift φ f) : AnySignature L := ⟨f.1,U.table⟩
theorem lifted_map {f : AnySignature E} (U : KeyLift φ f) :
    RH.mapAny φ (lifted φ U) = keyAny f := by
  exact congrArg (fun t => (⟨f.1,t⟩ : AnySignature E)) U.equation

def normalizedSplit {f a b : AnySignature E} (S : ProperSplit f a b)
    (hf : f.2 ≠ 0) (U : KeyLift φ f) :
    ProperSplit (lifted φ U) (lifted φ (leftLift φ S hf U))
      (lifted φ (rightLift φ S hf U)) where
  left_pos := S.left_pos
  right_pos := S.right_pos
  ports := S.ports
  scale := Units.mk0 (denominator φ S hf U) (denominator_nonzero φ S hf U)
  equation := by
    funext x
    apply φ.injective
    simp only [map_mul,Units.val_mk0]
    change φ (U.table x) = φ (denominator φ S hf U) *
      (φ (leftTable φ S hf U (fun i => x (S.ports (.inl i)))) *
        φ (rightTable φ S hf U (fun i => x (S.ports (.inr i)))))
    have hx := slice_map φ S hf U (fun i => x (S.ports (.inl i))) (fun i => x (S.ports (.inr i)))
    rw [joinWord_eta S x] at hx
    rw [hx]
    simp only [leftTable,rightTable,map_div₀,denominator,slice_map φ S hf U]
    field_simp [multiplier_nonzero S hf,
      firstWord_nonzero a.2 (S.factors_nonzero hf).1,
      firstWord_nonzero b.2 (S.factors_nonzero hf).2,leftWord,rightWord] <;> ring

def normalizedTree {f : AnySignature E} (t : FactorTree f) (hf : f.2 ≠ 0)
    (U : KeyLift φ f) : FactorTree (lifted φ U) :=
  match t with
  | .leaf _ p => .leaf _ ((prime_mapSignature_iff φ _).mp (by
      change Prime (RH.mapAny φ (lifted φ U))
      rw [lifted_map]
      exact prime_key p))
  | .split S l r => .split (normalizedSplit φ S hf U)
      (normalizedTree l (S.factors_nonzero hf).1 (leftLift φ S hf U))
      (normalizedTree r (S.factors_nonzero hf).2 (rightLift φ S hf U))

theorem normalizedTree_leaves {f : AnySignature E} (t : FactorTree f)
    (hf : f.2 ≠ 0) (U : KeyLift φ f) :
    ∀ u ∈ (normalizedTree φ t hf U).leaves,
      ∃ v ∈ t.leaves, RH.mapAny φ u = keyAny v := by
  revert hf U
  induction t with
  | leaf f p =>
    intro hf U
    intro u hu
    have he := Multiset.mem_singleton.mp hu
    subst u
    exact ⟨f,by simp [FactorTree.leaves],lifted_map φ U⟩
  | split S l r il ir =>
    intro hf U
    intro u hu
    rcases Multiset.mem_add.mp hu with hu | hu
    · obtain ⟨v,hv,he⟩ := il (S.factors_nonzero hf).1 (leftLift φ S hf U) u hu
      exact ⟨v,Multiset.mem_add.mpr (Or.inl hv),he⟩
    · obtain ⟨v,hv,he⟩ := ir (S.factors_nonzero hf).2 (rightLift φ S hf U) u hu
      exact ⟨v,Multiset.mem_add.mpr (Or.inr hv),he⟩

theorem mapAny_injective : Function.Injective (RH.mapAny φ) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m := congrArg Sigma.fst h
  subst m
  have he : RH.mapSignature φ f = RH.mapSignature φ g := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hf := Holant.LocalDrafts.MainChain.RingHomDescent.signature_injective φ he
  cases hf
  rfl

end Holant.LocalDrafts.Hardness.FrozenFactorNormalization
