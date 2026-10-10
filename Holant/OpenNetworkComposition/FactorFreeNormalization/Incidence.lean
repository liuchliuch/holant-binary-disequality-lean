import Holant.OpenNetworkComposition.OrdinaryNormalization.EmptyFree
import Holant.OpenNetworkComposition.ProjectiveContractionNormalize

/-! Exact normalization without any added vertex resource when every free
endpoint has an ordinary mate. The selected native X and its free-boundary
correction cancel; all original vertex labels and their port orders survive. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.FactorFreeNormalization
universe u v w z
variable {K : Type u} {V : Type v} {F : Type w} {E : Type z} {n : ℕ}

/-- No native edge has two free endpoints. -/
def OrdinaryMates (M : FiniteNetwork K V F E n) : Prop :=
  ∀f,∃p : Σv,Fin (M.shape.arity v),
    M.shape.ends ((M.shape.freeEdge f).1,!(M.shape.freeEdge f).2)=.inl p

variable (M : FiniteNetwork K V F E n) (f : F)
    (p : Σv,Fin (M.shape.arity v))
    (hp : M.shape.ends ((M.shape.freeEdge f).1,!(M.shape.freeEdge f).2)=.inl p)

abbrev remove : FiniteNetwork K V (FiniteShape.CutFree f) (M.shape.CutEdge f) n :=
  ProjectiveContraction.Normalize.network M f (M.shape.freeBoundary f) p
    (M.shape.free_boundary f) hp

/-- Surviving free ends retain their actual original edge-end occurrence. -/
theorem remove_freeEdge (g : FiniteShape.CutFree f) :
    (((remove M f p hp).shape.freeEdge g).1.val,
      ((remove M f p hp).shape.freeEdge g).2)=M.shape.freeEdge g.val := by
  apply M.shape.ends.injective
  have hg := congrArg (M.shape.cutEmbed f) ((remove M f p hp).shape.free_paired g)
  change M.shape.cutEmbed f (M.shape.cutEnds f ((remove M f p hp).shape.freeEdge g))=
    M.shape.cutEmbed f (.inr g) at hg
  simpa only [FiniteShape.cutEmbed_cutEnds,FiniteShape.cutEmbed_inr,
    M.shape.free_paired] using hg

/-- Removing one free/ordinary wire cannot create a free/free wire. -/
theorem remove_ordinaryMates (hm : OrdinaryMates M) : OrdinaryMates (remove M f p hp) := by
  intro g
  obtain ⟨q,hq⟩ := hm g.val
  refine ⟨q,?_⟩
  apply (M.shape.cutEmbed f).injective
  change M.shape.cutEmbed f (M.shape.cutEnds f
    (((remove M f p hp).shape.freeEdge g).1,!((remove M f p hp).shape.freeEdge g).2))=
    M.shape.cutEmbed f (.inl q)
  simp only [FiniteShape.cutEmbed_cutEnds,FiniteShape.cutEmbed_inl]
  have he := remove_freeEdge M f p hp g
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp only at h1 h2
  rw [h1,h2]
  exact hq

variable [CommSemiring K] [Fintype V] [Fintype F] [Fintype E]

/-- The normalization uses only original labels and preserves the exact
corrected tensor, including zero and disconnected scalar factors. -/
theorem exists_ordinary (hm : OrdinaryMates M) (family : SignatureFamily K)
    (hv : ∀v,(⟨M.shape.arity v,M.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,M.edge e=.disequality) :
    ∃N : Network K n,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=M.tensor := by
  classical
  have aux : ∀k : ℕ,∀ (F : Type w) (E : Type z) [Fintype F] [Fintype E],
      Fintype.card F=k → ∀M : FiniteNetwork K V F E n,
      OrdinaryMates M →
      (∀v,(⟨M.shape.arity v,M.vertex v⟩ : AnySignature K)∈family) →
      (∀e,M.edge e=.disequality) →
      ∃N : Network K n,
        (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
        (∀e,N.edge e=Signature.disequality) ∧ N.denote=M.tensor := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro F E _ _ hk M hm hv he
      rcases isEmpty_or_nonempty F with hF | hF
      · let : IsEmpty F := hF
        exact OrdinaryNormalization.exists_ordinary_of_isEmpty M family hv he
      · obtain ⟨f⟩ := hF
        obtain ⟨p,hp⟩ := hm f
        have hl : Fintype.card (FiniteShape.CutFree f)<k := by
          rw [←hk]
          exact Fintype.card_subtype_lt (x := f) (not_not.mpr rfl)
        obtain ⟨N,hvN,heN,hN⟩ := ih _ hl _ _ rfl (remove M f p hp)
          (remove_ordinaryMates M f p hp hm) hv
          (ProjectiveContraction.Normalize.network_native _ _ _ _ _ _ he)
        refine ⟨N,hvN,heN,hN.trans ?_⟩
        exact ProjectiveContraction.Normalize.network_tensor _ _ _ _ _ _ he
  exact aux _ F E rfl M hm hv he

end Holant.OpenNetworkComposition.FactorFreeNormalization
