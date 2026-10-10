import Holant.Tractable.Criteria
import Holant.Proofs.Reductions.SingleWeightCompletion.Family
import Holant.Proofs.Algorithms.TractXRestore

/-!
# Arbitrary-layout source normalization for the seven runtime alternatives

Zero/nullary deletion, prescribed K inverse, central restriction and ordered
completion are identified with the exact original predicates. Completion-layer
profiles range over the finite internally enumerable interval 0..arity. No
source-side existence claim is replaced by a supplied layer profile: profiles
are quantified in the final equivalence and are later enumerated by programmes.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {arity : Fin s → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i))
def family : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin s => (⟨arity i,G i⟩ : AnySignature AlgebraicComplex))
abbrev native (i : Fin s) := sourceKBasis.symm.action (G i)
def central (i : Fin s) := Signature.centralRestriction (native G i)

theorem k_range : kCoordinates (family G)=family (native G) := by
  ext f
  constructor
  · rintro ⟨g,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨⟨arity i,G i⟩,⟨i,rfl⟩,rfl⟩

theorem k_preprocess_range : kCoordinates (preprocess (family G))=preprocess (family (native G)) := by
  ext f
  constructor
  · rintro ⟨g,⟨⟨i,rfl⟩,hi,hn⟩,rfl⟩
    refine ⟨⟨i,rfl⟩,hi,?_⟩
    intro hz
    have he := congrArg sourceKBasis.action hz
    rw [InvertibleKernel.action_symm_action] at he
    exact hn (by simpa only [InvertibleKernel.action,Signature.coordinateAction_zero] using he)
  · rintro ⟨⟨i,rfl⟩,hi,hn⟩
    refine ⟨⟨arity i,G i⟩,⟨⟨i,rfl⟩,hi,?_⟩,rfl⟩
    intro hz
    change G i=0 at hz
    exact hn (by simp only [native,hz,
      InvertibleKernel.action,Signature.coordinateAction_zero])

private theorem nullary_charge {n : ℕ} (hn : n=0) (x : Fin n → Bool) : charge x=0 := by
  have hw := weight_le x
  have hz : weight x=0 := by omega
  simp [charge,hn,hz]

theorem commonSide_restore : CommonOneSided (preprocess (family G)) ↔
    CommonOneSided (family G) := by
  constructor
  · rintro (hp | hn)
    · left
      rintro _ ⟨i,rfl⟩ x hx
      by_cases hpos : 0<arity i
      · exact hp _ ⟨⟨i,rfl⟩,hpos,fun hz => hx (congrFun hz x)⟩ x hx
      · rw [nullary_charge (by omega : arity i=0) x]
    · right
      rintro _ ⟨i,rfl⟩ x hx
      by_cases hpos : 0<arity i
      · exact hn _ ⟨⟨i,rfl⟩,hpos,fun hz => hx (congrFun hz x)⟩ x hx
      · rw [nullary_charge (by omega : arity i=0) x]
  · rintro (hp | hn)
    · exact Or.inl (fun g hg => hp g hg.1)
    · exact Or.inr (fun g hg => hn g hg.1)

theorem central_preprocess_range : centralFamily (preprocess (family G))=
    preprocess (family (fun i => Signature.centralRestriction (G i))) := by
  ext f
  constructor
  · rintro ⟨g,⟨⟨i,rfl⟩,hi,hn⟩,hc,rfl⟩
    exact ⟨⟨i,rfl⟩,hi,hc⟩
  · rintro ⟨⟨i,rfl⟩,hi,hc⟩
    have hn : G i≠0 := by
      intro hz
      apply hc
      funext x
      simp [Signature.centralRestriction,hz]
    exact ⟨⟨arity i,G i⟩,⟨⟨i,rfl⟩,hi,hn⟩,hc,rfl⟩

/-- Both conjunctions concern the same original finite family, with exactly
one support sign for all its members. -/
theorem oneSided_iff : OneSidedAlternative (preprocess (family G)) ↔
    CommonOneSided (family (native G)) ∧ EOTract (preprocess (family (central G))) := by
  rw [OneSidedAlternative,k_preprocess_range,commonSide_restore,central_preprocess_range]
  rfl

/-- Strict signs force positive arity, so the prescribed deletion cannot erase
one of the two genuinely present support witnesses. -/
theorem bothSigns_restore : BothChargeSigns (preprocess (family G)) ↔ BothChargeSigns (family G) := by
  have pos {i : Fin s} {x : Fin (arity i) → Bool} (h : charge x≠0) : 0<arity i := by
    by_contra hn
    exact h (nullary_charge (by omega) x)
  constructor
  · rintro ⟨⟨g,hg,x,hx,hneg⟩,⟨k,hk,y,hy,hpos⟩⟩
    exact ⟨⟨g,hg.1,x,hx,hneg⟩,⟨k,hk.1,y,hy,hpos⟩⟩
  · rintro ⟨⟨g,⟨i,rfl⟩,x,hx,hneg⟩,⟨k,⟨j,rfl⟩,y,hy,hpos⟩⟩
    exact ⟨⟨_,⟨⟨i,rfl⟩,pos (ne_of_lt hneg),fun hz => hx (congrFun hz x)⟩,x,hx,hneg⟩,
      ⟨_,⟨⟨j,rfl⟩,pos (ne_of_gt hpos),fun hz => hy (congrFun hz y)⟩,y,hy,hpos⟩⟩

def Profile := (i : Fin s) → Fin (arity i+1)
def layers (p : Profile (s:=s) (arity:=arity)) (i : Fin s) : ℕ := (p i).val
def completedArity (p : Profile (s:=s) (arity:=arity)) (i : Fin s) : ℕ := arity i+SingleWeightCompletion.extra (arity i) (layers p i)
def completed (p : Profile (s:=s) (arity:=arity)) (i : Fin s) : Signature AlgebraicComplex (completedArity p i) := SingleWeightCompletion.completed (G i) (layers p i)

theorem completed_positive_iff (p : Profile (s:=s) (arity:=arity)) (i : Fin s) :
    0<completedArity p i ↔ 0<arity i := by
  have hd : (p i).val≤arity i := Nat.le_of_lt_succ (p i).isLt
  simp only [completedArity]
  constructor
  · intro hp
    by_contra hn
    have ha : arity i=0 := by omega
    have hz : (p i).val=0 := by omega
    simp [layers,ha,hz,SingleWeightCompletion.extra] at hp
  · intro hp
    exact Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _)

theorem completion_preprocess_range (p : Profile (s:=s) (arity:=arity))
    (hp : ∀ i, Signature.SingleLayer (G i) (layers p i)) :
    completionFamily (preprocess (family G))=preprocess (family (completed G p)) := by
  ext f
  constructor
  · rintro ⟨g,⟨⟨i,rfl⟩,hi,hn⟩,_,d,hd,rfl⟩
    have he : d=layers p i := Signature.singleLayer_unique hn hd (hp i)
    subst d
    have hlabel := SingleWeightCompletion.completed_exact (G i) (layers p i)
    change (⟨completedArity p i,completed G p i⟩ : AnySignature AlgebraicComplex)=Signature.completeToEO (G i) (layers p i) at hlabel
    change Signature.completeToEO (G i) (layers p i) ∈ _
    rw [←hlabel]
    exact ⟨⟨i,rfl⟩,(completed_positive_iff p i).mpr hi,
      (SingleWeightCompletion.completed_nonzero_iff (G i) (layers p i)).mpr hn⟩
  · rintro ⟨⟨i,rfl⟩,hi,hn⟩
    have hnG := (SingleWeightCompletion.completed_nonzero_iff (G i) (layers p i)).mp hn
    exact ⟨⟨arity i,G i⟩,⟨⟨i,rfl⟩,(completed_positive_iff p i).mp hi,hnG⟩,
      hnG,layers p i,hp i,(SingleWeightCompletion.completed_exact (G i) (layers p i))⟩

private theorem bounded_layer (i : Fin s) (h : ∃d,Signature.SingleLayer (G i) d) :
    ∃d≤arity i,Signature.SingleLayer (G i) d := by
  classical
  by_cases hz : G i=0
  · exact ⟨0,Nat.zero_le _,by simp [Signature.SingleLayer,hz]⟩
  · obtain ⟨d,hd⟩ := h
    have hx : ∃ x, G i x≠0 := by
      by_contra hn
      push_neg at hn
      exact hz (funext hn)
    obtain ⟨x,hx⟩ := hx
    have hw := hd.weight_of_nezero hx
    exact ⟨d,hw ▸ weight_le x,hd⟩

theorem layerProfiles_iff : (∀f∈preprocess (family G),∃d,Signature.SingleLayer f.2 d) ↔
    ∃p : Profile (s:=s) (arity:=arity), ∀i,Signature.SingleLayer (G i) (layers p i) := by
  constructor
  · intro h
    have he (i : Fin s) : ∃d≤arity i,Signature.SingleLayer (G i) d := by
      apply bounded_layer G i
      by_cases hz : G i=0
      · exact ⟨0,by simp [Signature.SingleLayer,hz]⟩
      · by_cases hi : 0<arity i
        · exact h _ ⟨⟨i,rfl⟩,hi,hz⟩
        · refine ⟨0,?_⟩
          intro x hx
          have hw := weight_le x
          have he : weight x=0 := by omega
          exact False.elim (hx he)
    choose d hd hspec using he
    exact ⟨fun i => ⟨d i,Nat.lt_succ_of_le (hd i)⟩,hspec⟩
  · rintro ⟨p,hp⟩ f ⟨⟨i,rfl⟩,_⟩
    exact ⟨layers p i,hp i⟩

/-- Exact source clause (2), with bounded profile search and both strict signs
retained for the whole original native-coordinate family. -/
theorem singleWeight_iff : SingleWeightAlternative (preprocess (family G)) ↔
    BothChargeSigns (family (native G)) ∧
      ∃p : Profile (s:=s) (arity:=arity),
        (∀i,Signature.SingleLayer (native G i) (layers p i)) ∧
        EOTract (preprocess (family (completed (native G) p))) := by
  rw [SingleWeightAlternative,k_preprocess_range,bothSigns_restore,layerProfiles_iff]
  constructor
  · rintro ⟨⟨p,hp⟩,hs,he⟩
    exact ⟨hs,p,hp,(completion_preprocess_range (native G) p hp) ▸ he⟩
  · rintro ⟨hs,p,hp,he⟩
    exact ⟨⟨p,hp⟩,hs,(completion_preprocess_range (native G) p hp).symm ▸ he⟩


/-- All seven clauses, with restoration handled before the real four-clause
and matching controllers; no recognition answer is assumed. -/
theorem tract_iff : Tract (family G) ↔
    OneSidedAlternative (preprocess (family G)) ∨ SingleWeightAlternative (preprocess (family G)) ∨
      MatchingAlternative (family G) ∨ TractX (family G) := by
  have hf : (preprocess (family G)).Finite :=
    (Set.finite_range (fun i : Fin s => (⟨arity i,G i⟩ : AnySignature AlgebraicComplex))).subset (fun _ h => h.1)
  have hm : MatchingAlternative (preprocess (family G)) ↔ MatchingAlternative (family G) :=
    ⟨TractXRestore.matching_restore,fun h => h.mono_family (fun _ hf => hf.1)⟩
  rw [←hm]
  simp only [Tract,TractX,hf,true_and,TractCore,TractXCore]
  tauto

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenCriterionNormalization
