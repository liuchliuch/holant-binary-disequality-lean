import Holant.Proofs.Hardness.GeneralEOPhaseExtractionLoopTomography
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionFieldBridge

/-! A nonzero central antiselfdual graph supplies an actual nonzero signed
binary. The descent uses coordinate permutations and native disequality
self-loops only, and retains every original vertex label. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSkewPhaseExtraction
open Holant Holant.Complexity FixedGadgetSubstitution
namespace F
export SelfDualPinObstruction (flip)
end F
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote reboundaryLabels)
end R
namespace D
export GeneralEOPhaseExtractionDistance (loop loop_denote labels exact native central)
end D
namespace T
export GeneralEOPhaseExtractionLoopTomography (merge merge_denote ext_of_merges merge_flip)
end T
namespace B
export GeneralEOPhaseExtractionFieldBridge (family map_exact map_native map_central
  rebuild labels rebuild_exact rebuild_native map_rebuild)
end B
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {a : ℕ → ℕ}

def Skew (f : Signature ℂ n) : Prop := ∀x,f (F.flip x)= -f x

theorem merge_skew (f : Signature ℂ (n+2)) (hf : Skew f)
    (e : Equiv.Perm (Fin (n+2))) : Skew (T.merge f e) := by
  intro x
  have hh := congrFun (T.merge_flip f e) x
  rw [←hh]
  change ∀x,f (F.flip x)= -f x at hf
  simp only [T.merge,hf]
  ring

theorem exists_nonzero_merge (f : Signature ℂ (n+3))
    (hE : Signature.CentralSupport f) (h0 : ∃x,f x≠0) :
    ∃e : Equiv.Perm (Fin (n+3)), ∃x,T.merge f e x≠0 := by
  classical
  by_contra h
  push Not at h
  have he : f=0 := T.ext_of_merges f 0 hE (by intro x hx; rfl) (by
    intro e
    funext x
    simpa [T.merge] using h e x)
  obtain ⟨x,hx⟩ := h0
  exact hx (congrFun he x)

theorem binary_signed (S : Network ℂ 2) (hE : Signature.CentralSupport S.denote)
    (hS : Skew S.denote) (h0 : ∃x,S.denote x≠0) :
    ∃t : ℂ,t≠0 ∧ GeneralEOPhaseExtractionNetwork.Signed S t := by
  have h00 : S.denote ![false,false]=0 := hE _ (by decide)
  have h11 : S.denote ![true,true]=0 := hE _ (by decide)
  have hf : F.flip (![false,true] : Fin 2 → Bool)=![true,false] := by
    funext i
    fin_cases i <;> rfl
  have h10 : S.denote ![true,false]= -S.denote ![false,true] := by
    simpa only [hf] using hS ![false,true]
  refine ⟨S.denote ![false,true],?_,h00,rfl,h10,h11⟩
  intro hz
  obtain ⟨x,hx⟩ := h0
  have hword : x=![x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  apply hx
  rw [hword]
  cases x 0 <;> cases x 1 <;> simp [h00,h11,h10,hz]

variable (G : (i : Fin s) → Signature ℂ (a i.val))

/-- The signed binary is a real network, not an added signature or an oracle. -/
theorem signed_binary (n : ℕ) :
    ∀ (S : Network ℂ n) (SL : Labelling S.shape s 1 a),
      LabelledNetwork.Exact G S SL → (∀e,S.edge e=Signature.disequality) →
      Signature.CentralSupport S.denote → Skew S.denote → (∃x,S.denote x≠0) →
      ∃ (Q : Network ℂ 2) (QL : Labelling Q.shape s 1 a) (t : ℂ),
        LabelledNetwork.Exact G Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
        t≠0 ∧ GeneralEOPhaseExtractionNetwork.Signed Q t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S SL hL hN hE hS h0
    by_cases hn0 : n=0
    · subst n
      obtain ⟨x,hx⟩ := h0
      have hflip : F.flip x=x := by funext i; exact Fin.elim0 i
      have hs := hS x
      rw [hflip] at hs
      have hz : S.denote x=0 := by linear_combination (1/2 : ℂ)*hs
      exact (hx hz).elim
    by_cases hn1 : n=1
    · subst n
      obtain ⟨x,hx⟩ := h0
      exact (hx (hE x (by omega))).elim
    by_cases hn2 : n=2
    · subst n
      obtain ⟨t,ht,hSt⟩ := binary_signed S hE hS h0
      exact ⟨S,SL,t,hL,hN,ht,hSt⟩
    obtain ⟨k,rfl⟩ : ∃k,n=k+3 := ⟨n-3,by omega⟩
    obtain ⟨e,x,hx⟩ := exists_nonzero_merge S.denote hE h0
    let U := R.reboundary S e
    let UL := R.reboundaryLabels S SL e
    have hUE : Signature.CentralSupport U.denote :=
      GeneralEOCentralHoleCoordinates.reboundary_central S e.symm hE
    apply ih (k+1) (by omega) (D.loop U) (D.labels U UL)
      (D.exact G U UL hL) (D.native U hN) (D.central U hUE)
    · rw [T.merge_denote]
      exact merge_skew S.denote hS e
    · exact ⟨x,by simpa only [U,T.merge_denote] using hx⟩

variable {K : Type*} [Field K]
variable (H : (i : Fin s) → Signature K (a i.val)) (φ : K →+* ℂ)

/-- Return the native signed graph over the exact original coefficient field. -/
theorem original_signed_binary (S : Network K n) (SL : Labelling S.shape s 1 a)
    (hL : LabelledNetwork.Exact H S SL) (hN : ∀e,S.edge e=Signature.disequality)
    (hE : Signature.CentralSupport S.denote) (hS : Skew (S.map φ).denote)
    (h0 : ∃x,(S.map φ).denote x≠0) :
    ∃ (Q : Network K 2) (QL : Labelling Q.shape s 1 a) (t : ℂ),
      LabelledNetwork.Exact H Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
      t≠0 ∧ GeneralEOPhaseExtractionNetwork.Signed (Q.map φ) t := by
  obtain ⟨Q,QL,t,hQL,hQN,ht,hQt⟩ := signed_binary (B.family H φ) n
    (S.map φ) SL (B.map_exact H φ S SL hL) (B.map_native φ S hN)
    (B.map_central φ S hE) hS h0
  refine ⟨B.rebuild H Q QL,B.labels H Q QL,t,B.rebuild_exact H Q QL,
    B.rebuild_native H Q QL,ht,?_⟩
  rw [B.map_rebuild H φ Q QL hQL hQN]
  exact hQt

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSkewPhaseExtraction
